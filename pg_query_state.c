/*
 * pg_query_state.c
 *		Extract information about query state from other backend
 *
 * Copyright (c) 2016-2016, Postgres Professional
 *
 *	  contrib/pg_query_state/pg_query_state.c
 * IDENTIFICATION
 */

#include <postgres.h>

#include "access/htup_details.h"
#include "catalog/pg_type.h"
#include "commands/explain.h"
#include "funcapi.h"
#include "executor/execParallel.h"
#include "executor/executor.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pg_list.h"
#include "nodes/print.h"
#include "pgstat.h"
#include "postmaster/bgworker.h"
#include "storage/ipc.h"
#include "storage/s_lock.h"
#include "storage/spin.h"
#include "storage/shm_mq.h"
#include "storage/procarray.h"
#include "storage/procsignal.h"
#include "storage/shm_toc.h"
#include "utils/guc.h"
#include "utils/timestamp.h"

#ifdef PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif

#define	PG_QS_MODULE_KEY	0xCA94B108
#define	PG_QUERY_STATE_KEY	0
#define	EXECUTOR_TRACE_KEY	1

#define	QUEUE_SIZE			(16 * 1024)
#define BASE_SIZEOF_SHM_MQ_MSG (offsetof(shm_mq_msg, stack_depth))

#define TIMINIG_OFF_WARNING 1
#define BUFFERS_OFF_WARNING 2

#define TEXT_CSTR_CMP(text, cstr) \
	(memcmp(VARDATA(text), (cstr), VARSIZE(text) - VARHDRSZ))

/* GUC variables */
bool pg_qs_enable = true;
bool pg_qs_timing = false;
bool pg_qs_buffers = false;
bool pg_qs_trace = false;

/* Saved hook values in case of unload */
static ExecutorStart_hook_type prev_ExecutorStart = NULL;
static ExecutorRun_hook_type prev_ExecutorRun = NULL;
static ExecutorFinish_hook_type prev_ExecutorFinish = NULL;
static ExecutorEnd_hook_type prev_ExecutorEnd = NULL;
static shmem_startup_hook_type prev_shmem_startup_hook = NULL;
static PostExecProcNode_hook_type prev_postExecProcNode = NULL;

void		_PG_init(void);
void		_PG_fini(void);

/* hooks defined in this module */
static void qs_ExecutorStart(QueryDesc *queryDesc, int eflags);
static void qs_ExecutorRun(QueryDesc *queryDesc, ScanDirection direction, uint64 count);
static void qs_ExecutorFinish(QueryDesc *queryDesc);
static void qs_ExecutorEnd(QueryDesc *queryDesc);
static void qs_postExecProcNode(PlanState *planstate, TupleTableSlot *result);

/* Global variables */
List 					*QueryDescStack = NIL;
static ProcSignalReason  QueryStatePollReason = INVALID_PROCSIGNAL;
static bool 			 module_initialized = false;
static const char		*be_state_str[] = {						/* BackendState -> string repr */
							"undefined",						/* STATE_UNDEFINED */
							"idle",								/* STATE_IDLE */
							"active",							/* STATE_RUNNING */
							"idle in transaction",				/* STATE_IDLEINTRANSACTION */
							"fastpath function call",			/* STATE_FASTPATH */
							"idle in transaction (aborted)",	/* STATE_IDLEINTRANSACTION_ABORTED */
							"disabled",							/* STATE_DISABLED */
						};

typedef struct
{
	slock_t	 mutex;		/* protect concurrent access to `userid` */
	Oid		 userid;
	Latch	*caller;
} RemoteUserIdResult;

/*
 * Result status on query state request from asked backend
 */
typedef enum
{
	BACKEND_DIED,
	QUERY_NOT_RUNNING,		/* Backend doesn't execute any query */
	STAT_DISABLED,			/* Collection of execution statistics is disabled */
	QS_RETURNED				/* Backend succesfully returned its query state */
} pgqsResultCode;

/*
 * Structure of stack frame of fucntion call which resulted from analyze of
 * 	query state
 */
typedef struct
{
	const char	*query;
	const char	*plan;
} StackFrame;

typedef struct
{
	PGPROC	*proc;
	List	*frames;
} ProcState;

/*
 *	Format of transmited data through message queue
 */
/* typedef struct */
/* { */
	/* int		length;							 *//* size of message record, for */
											   /* sanity check */
	/* PGPROC	*proc; */
	/* pgqsResultCode	result_code; */
	/* int		warnings;						[> bitmap of warnings <] */
	/* int		stack_depth; */
	/* char	stack[FLEXIBLE_ARRAY_MEMBER];	 *//* sequencially laid out stack */
											   /* frames in form of text records */
/* } shm_mq_msg; */

/* pg_query_state arguments */
typedef struct
{
	Oid		userid;
	bool 	verbose;
	bool	costs;
	bool	timing;
	bool	buffers;
	bool	triggers;
	ExplainFormat format;
} pgqsParameters;

/*
 * Kinds of trace commands
 */
typedef enum
{
	STEP,
	CONTINUE
} trace_cmd;

/*
 * Trace command transmitted to counterpart
 */
typedef struct
{
	trace_cmd	command;
	pid_t 		tracer;
	pid_t 		traceable;
} trace_request;

extern void SendQueryState(void);
static pgqsResultCode GetRemoteBackendQueryState(PGPROC *proc,
												 bool verbose,
												 bool costs,
												 bool timing,
												 bool buffers,
												 bool triggers,
												 ExplainFormat format,
												 List **result,
												 int *warnings);

/* Shared memory variables */
shm_toc			*toc = NULL;
pgqsParameters	*params = NULL;
trace_request	*trace_req = NULL;
shm_mq 			*mq = NULL;

/*
 * Estimate amount of shared memory needed.
 */
static Size
pg_qs_shmem_size()
{
	shm_toc_estimator	e;
	Size				size;
	int					nkeys;

	shm_toc_initialize_estimator(&e);

	nkeys = 3;

	shm_toc_estimate_chunk(&e, sizeof(trace_request));
	shm_toc_estimate_chunk(&e, sizeof(pgqsParameters));
	shm_toc_estimate_chunk(&e, (Size) QUEUE_SIZE);

	shm_toc_estimate_keys(&e, nkeys);
	size = shm_toc_estimate(&e);

	return size;
}

/*
 * Distribute shared memory.
 */
static void
pg_qs_shmem_startup(void)
{
	bool	found;
	Size	shmem_size = pg_qs_shmem_size();
	void	*shmem;
	int		num_toc = 0;

	shmem = ShmemInitStruct("pg_query_state", shmem_size, &found);
	if (!found)
	{
		toc = shm_toc_create(PG_QS_MODULE_KEY, shmem, shmem_size);

		params = shm_toc_allocate(toc, sizeof(pgqsParameters));
		shm_toc_insert(toc, num_toc++, params);

		trace_req = shm_toc_allocate(toc, sizeof(trace_request));
		shm_toc_insert(toc, num_toc++, trace_req);
		MemSet(trace_req, 0, sizeof(trace_request));

		mq = shm_toc_allocate(toc, QUEUE_SIZE);
		shm_toc_insert(toc, num_toc++, mq);
	}
	else
	{
		toc = shm_toc_attach(PG_QS_MODULE_KEY, shmem);

		params = shm_toc_lookup(toc, num_toc++);
		trace_req = shm_toc_lookup(toc, num_toc++);
		mq = shm_toc_lookup(toc, num_toc++);
	}

	if (prev_shmem_startup_hook)
		prev_shmem_startup_hook();

	module_initialized = true;
}

/*
 * Module load callback
 */
void
_PG_init(void)
{
	if (!process_shared_preload_libraries_in_progress)
		return;

	/*
	 * Request additional shared resources.  (These are no-ops if we're not in
	 * the postmaster process.)  We'll allocate or attach to the shared
	 * resources in qs_shmem_startup().
	 */
	RequestAddinShmemSpace(pg_qs_shmem_size());

	/* Register interrupt on custom signal of polling query state */
	QueryStatePollReason = RegisterCustomProcSignalHandler(SendQueryState);
	if (QueryStatePollReason == INVALID_PROCSIGNAL)
	{
		ereport(WARNING, (errcode(ERRCODE_INSUFFICIENT_RESOURCES),
					errmsg("pg_query_state isn't loaded: insufficient custom ProcSignal slots")));
		return;
	}

	/* Define custom GUC variables */
	DefineCustomBoolVariable("pg_query_state.enable",
							 "Enable module.",
							 NULL,
							 &pg_qs_enable,
							 true,
							 PGC_SUSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
	DefineCustomBoolVariable("pg_query_state.enable_timing",
							 "Collect timing data, not just row counts.",
							 NULL,
							 &pg_qs_timing,
							 false,
							 PGC_SUSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
	DefineCustomBoolVariable("pg_query_state.enable_buffers",
							 "Collect buffer usage.",
							 NULL,
							 &pg_qs_buffers,
							 false,
							 PGC_SUSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
	DefineCustomBoolVariable("pg_query_state.executor_trace",
							 "Turn on trace of plan execution.",
							 NULL,
							 &pg_qs_trace,
							 false,
							 PGC_SUSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
	EmitWarningsOnPlaceholders("pg_query_state");

	/* Install hooks */
	prev_ExecutorStart = ExecutorStart_hook;
	ExecutorStart_hook = qs_ExecutorStart;
	prev_ExecutorRun = ExecutorRun_hook;
	ExecutorRun_hook = qs_ExecutorRun;
	prev_ExecutorFinish = ExecutorFinish_hook;
	ExecutorFinish_hook = qs_ExecutorFinish;
	prev_ExecutorEnd = ExecutorEnd_hook;
	ExecutorEnd_hook = qs_ExecutorEnd;
	prev_shmem_startup_hook = shmem_startup_hook;
	shmem_startup_hook = pg_qs_shmem_startup;
	prev_postExecProcNode = postExecProcNode_hook;
}

/*
 * Module unload callback
 */
void
_PG_fini(void)
{
	module_initialized = false;

	/* clear global state */
	list_free(QueryDescStack);
	AssignCustomProcSignalHandler(QueryStatePollReason, NULL);

	/* Uninstall hooks. */
	ExecutorStart_hook = prev_ExecutorStart;
	ExecutorRun_hook = prev_ExecutorRun;
	ExecutorFinish_hook = prev_ExecutorFinish;
	ExecutorEnd_hook = prev_ExecutorEnd;
	shmem_startup_hook = prev_shmem_startup_hook;
	postExecProcNode_hook = prev_postExecProcNode;
}

/*
 * In trace mode suspend query execution until other backend resumes it
 */
static void
suspend_traceable_query()
{
	for (;;)
	{
		/* Check whether current backend is traced */
		if (MyProcPid == trace_req->traceable)
		{
			PGPROC *tracer = BackendPidGetProc(trace_req->tracer);

			Assert(tracer != NULL);

			if (trace_req->command == CONTINUE)
				postExecProcNode_hook = prev_postExecProcNode;
			trace_req->traceable = 0;
			SetLatch(&tracer->procLatch);
			break;
		}

		/*
		 * Wait for our latch to be set.  It might already be set for some
		 * unrelated reason, but that'll just result in one extra trip through
		 * the loop.  It's worth it to avoid resetting the latch at top of
		 * loop, because setting an already-set latch is much cheaper than
		 * setting one that has been reset.
		 */
		WaitLatch(MyLatch, WL_LATCH_SET, 0);

		/* An interrupt may have occurred while we were waiting. */
		CHECK_FOR_INTERRUPTS();

		/* Reset the latch so we don't spin. */
		ResetLatch(MyLatch);
	}
}

/*
 * postExecProcNode_hook:
 * 		interrupt before execution next node of plan tree
 * 		until other process resumes it through function calls:
 * 			'executor_step(<pid>)'
 * 			'executor_continue(<pid>)'
 */
static void
qs_postExecProcNode(PlanState *planstate, TupleTableSlot *result)
{
	suspend_traceable_query();

	if (prev_postExecProcNode)
		prev_postExecProcNode(planstate, result);
}

/*
 * ExecutorStart hook:
 * 		set up flags to store runtime statistics,
 * 		push current query description in global stack
 */
static void
qs_ExecutorStart(QueryDesc *queryDesc, int eflags)
{
	PG_TRY();
	{
		/* Enable per-node instrumentation */
		if (pg_qs_enable && ((eflags & EXEC_FLAG_EXPLAIN_ONLY) == 0))
		{
			queryDesc->instrument_options |= INSTRUMENT_ROWS;
			if (pg_qs_timing)
				queryDesc->instrument_options |= INSTRUMENT_TIMER;
			if (pg_qs_buffers)
				queryDesc->instrument_options |= INSTRUMENT_BUFFERS;
		}

		if (prev_ExecutorStart)
			prev_ExecutorStart(queryDesc, eflags);
		else
			standard_ExecutorStart(queryDesc, eflags);

		/* push structure about current query in global stack */
		QueryDescStack = lcons(queryDesc, QueryDescStack);

		/* set/reset hook for trace mode before start of upper level query */
		if (list_length(QueryDescStack) == 1)
			postExecProcNode_hook = (pg_qs_enable && pg_qs_trace) ?
										qs_postExecProcNode : prev_postExecProcNode;

		/* suspend traceable query if it is not continued (hook is not thrown off) */
		if (postExecProcNode_hook == qs_postExecProcNode)
			suspend_traceable_query();
	}
	PG_CATCH();
	{
		QueryDescStack = NIL;
		PG_RE_THROW();
	}
	PG_END_TRY();
}

/*
 * ExecutorRun:
 * 		Catch any fatal signals
 */
static void
qs_ExecutorRun(QueryDesc *queryDesc, ScanDirection direction, uint64 count)
{
	PG_TRY();
	{
		if (prev_ExecutorRun)
			prev_ExecutorRun(queryDesc, direction, count);
		else
			standard_ExecutorRun(queryDesc, direction, count);
	}
	PG_CATCH();
	{
		QueryDescStack = NIL;
		PG_RE_THROW();
	}
	PG_END_TRY();
}

/*
 * ExecutorFinish:
 * 		Catch any fatal signals
 */
static void
qs_ExecutorFinish(QueryDesc *queryDesc)
{
	PG_TRY();
	{
		if (prev_ExecutorFinish)
			prev_ExecutorFinish(queryDesc);
		else
			standard_ExecutorFinish(queryDesc);
	}
	PG_CATCH();
	{
		QueryDescStack = NIL;
		PG_RE_THROW();
	}
	PG_END_TRY();
}

/*
 * ExecutorEnd hook:
 * 		pop current query description from global stack
 */
static void
qs_ExecutorEnd(QueryDesc *queryDesc)
{
	PG_TRY();
	{
		QueryDescStack = list_delete_first(QueryDescStack);

		if (prev_ExecutorEnd)
			prev_ExecutorEnd(queryDesc);
		else
			standard_ExecutorEnd(queryDesc);
	}
	PG_CATCH();
	{
		QueryDescStack = NIL;
		PG_RE_THROW();
	}
	PG_END_TRY();
}

/*
 * Find PgBackendStatus entry
 */
static PgBackendStatus *
search_be_status(int pid)
{
	int beid;

	if (pid <= 0)
		return NULL;

	for (beid = 1; beid <= pgstat_fetch_stat_numbackends(); beid++)
	{
		PgBackendStatus *be_status = pgstat_fetch_stat_beentry(beid);

		if (be_status && be_status->st_procpid == pid)
			return be_status;
	}

	return NULL;
}

/*
 * Init userlock
 */
static void
init_lock_tag(LOCKTAG *tag, uint32 key)
{
	tag->locktag_field1 = PG_QS_MODULE_KEY;
	tag->locktag_field2 = key;
	tag->locktag_field3 = 0;
	tag->locktag_field4 = 0;
	tag->locktag_type = LOCKTAG_USERLOCK;
	tag->locktag_lockmethodid = USER_LOCKMETHOD;
}

/*
 * Structure of stack frame of fucntion call which transfers through message queue
 */
typedef struct
{
	text	*query;
	text	*plan;
} stack_frame1;

/*
 *	Convert serialized stack frame into stack_frame1 record
 *		Increment '*src' pointer to the next serialized stack frame
 */
static stack_frame1 *
deserialize_stack_frame(char **src)
{
	stack_frame1 *result = palloc(sizeof(stack_frame1));
	text		*query = (text *) *src,
				*plan = (text *) (*src + INTALIGN(VARSIZE(query)));

	result->query = palloc(VARSIZE(query));
	memcpy(result->query, query, VARSIZE(query));
	result->plan = palloc(VARSIZE(plan));
	memcpy(result->plan, plan, VARSIZE(plan));

	*src = (char *) plan + INTALIGN(VARSIZE(plan));
	return result;
}

/*
 * Convert serialized stack frames into List of stack_frame1 records
 */
static List *
deserialize_stack(char *src, int stack_depth)
{
	List 	*result = NIL;
	char	*curr_ptr = src;
	int		i;

	for (i = 0; i < stack_depth; i++)
	{
		stack_frame1	*frame = deserialize_stack_frame(&curr_ptr);
		result = lappend(result, frame);
	}

	return result;
}

/*
 * Implementation of pg_query_state function
 */
PG_FUNCTION_INFO_V1(pg_query_state);
Datum
pg_query_state(PG_FUNCTION_ARGS)
{
	/* multicall context type */
	typedef struct
	{
		ListCell	*proc_cursor;
		ListCell 	*frame_cursor;
		int			 frame_index;
		List		*ProcState;
	} pgqsFuncCtx;

	FuncCallContext	*funcctx;
	/* pgqsFuncCtx		*fctx; */
	/* const int		N_ATTRS = 5; */
	pid_t			pid = PG_GETARG_INT32(0);

	if (SRF_IS_FIRSTCALL())
	{
		LOCKTAG			 tag;
		bool			 verbose = PG_GETARG_BOOL(1),
						 costs = PG_GETARG_BOOL(2),
						 timing = PG_GETARG_BOOL(3),
						 buffers = PG_GETARG_BOOL(4),
						 triggers = PG_GETARG_BOOL(5);
		text			*format_text = PG_GETARG_TEXT_P(6);
		ExplainFormat	 format;
		PGPROC			*proc;
		pgqsResultCode	 result_code;
		List			*proc_states;
		int				 warnings;

		if (!module_initialized)
			goto module_not_initilized;

		if (pid == MyProcPid)
			goto address_to_current_process;

		proc = BackendPidGetProc(pid);
		if (!proc || proc->backendId == InvalidBackendId)
			goto invalid_backend;

		if (TEXT_CSTR_CMP(format_text, "text") == 0)
			format = EXPLAIN_FORMAT_TEXT;
		else if (TEXT_CSTR_CMP(format_text, "xml") == 0)
			format = EXPLAIN_FORMAT_XML;
		else if (TEXT_CSTR_CMP(format_text, "json") == 0)
			format = EXPLAIN_FORMAT_JSON;
		else if (TEXT_CSTR_CMP(format_text, "yaml") == 0)
			format = EXPLAIN_FORMAT_YAML;
		else
			goto unrecognized_format;

		/*
		 * init and acquire lock that protects from concurrent access to shared
		 * memory intended for query state transmission
		 */
		init_lock_tag(&tag, PG_QUERY_STATE_KEY);
		LockAcquire(&tag, ExclusiveLock, false, false);

		/* if (!(superuser() || GetUserId() == counterpart_user_id)) */
			/* ereport(ERROR, (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE), */
							/* errmsg("permission denied"))); */

		result_code = GetRemoteBackendQueryState(proc,
												 verbose,
												 costs,
												 timing,
												 buffers,
												 triggers,
												 format,
												 &proc_states,
												 &warnings);
		/* msg = (shm_mq_msg *) linitial(msgs); */

		funcctx = SRF_FIRSTCALL_INIT();
		/* switch (msg->result_code) */
		/* { */
			/* case QUERY_NOT_RUNNING: */
				/* { */
					/* PgBackendStatus	*be_status = search_be_status(pid); */

					/* if (be_status) */
						/* elog(INFO, "state of backend is %s", */
								/* be_state_str[be_status->st_state - STATE_UNDEFINED]); */
					/* else */
						/* elog(INFO, "backend is not running query"); */

					/* LockRelease(&tag, ExclusiveLock, false); */
					/* SRF_RETURN_DONE(funcctx); */
				/* } */
			/* case STAT_DISABLED: */
				/* elog(INFO, "query execution statistics disabled"); */
				/* LockRelease(&tag, ExclusiveLock, false); */
				/* SRF_RETURN_DONE(funcctx); */
			/* default: */
				/* break; */
		/* } */

		SRF_RETURN_DONE(funcctx);

		/* TupleDesc	tupdesc; */
		/* ListCell	*i; */
		/* int64		max_calls = 0; */
		/* MemoryContext	oldcontext; */

		/* [> print warnings if exist <] */
		/* if (msg->warnings & TIMINIG_OFF_WARNING) */
			/* ereport(WARNING, (errcode(ERRCODE_WARNING), */
						/* errmsg("timing statistics disabled"))); */
		/* if (msg->warnings & BUFFERS_OFF_WARNING) */
			/* ereport(WARNING, (errcode(ERRCODE_WARNING), */
						/* errmsg("buffers statistics disabled"))); */

		/* oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx); */

		/* [> save stack of calls and current cursor in multicall context <] */
		/* fctx = (pgqsFuncCtx *) palloc(sizeof(pgqsFuncCtx)); */
		/* fctx->procs = NIL; */
		/* foreach(i, msgs) */
		/* { */
			/* List 		*qs_stack; */
			/* shm_mq_msg	*msg = (shm_mq_msg *) lfirst(i); */
			/* ProcCtx	*p_state = (ProcCtx *) palloc(sizeof(ProcCtx)); */

			/* qs_stack = deserialize_stack(msg->stack, msg->stack_depth); */

			/* p_state->proc = msg->proc; */
			/* p_state->stack = qs_stack; */
			/* p_state->frame_index = 0; */
			/* p_state->frame_cursor = list_head(qs_stack); */

			/* fctx->procs = lappend(fctx->procs, p_state); */

			/* max_calls += list_length(qs_stack); */
		/* } */
		/* fctx->proc_cursor = list_head(fctx->procs); */

		/* funcctx->user_fctx = fctx; */
		/* funcctx->max_calls = max_calls; */

		/* [> Make tuple descriptor <] */
		/* tupdesc = CreateTemplateTupleDesc(N_ATTRS, false); */
		/* TupleDescInitEntry(tupdesc, (AttrNumber) 1, "pid", INT4OID, -1, 0); */
		/* TupleDescInitEntry(tupdesc, (AttrNumber) 2, "frame_number", INT4OID, -1, 0); */
		/* TupleDescInitEntry(tupdesc, (AttrNumber) 3, "query_text", TEXTOID, -1, 0); */
		/* TupleDescInitEntry(tupdesc, (AttrNumber) 4, "plan", TEXTOID, -1, 0); */
		/* TupleDescInitEntry(tupdesc, (AttrNumber) 5, "leader_pid", INT4OID, -1, 0); */
		/* funcctx->tuple_desc = BlessTupleDesc(tupdesc); */

		/* LockRelease(&tag, ExclusiveLock, false); */
		/* MemoryContextSwitchTo(oldcontext); */
	/* } */

	/* [> restore function multicall context <] */
	/* funcctx = SRF_PERCALL_SETUP(); */
	/* fctx = funcctx->user_fctx; */

	/* if (funcctx->call_cntr < funcctx->max_calls) */
	/* { */
		/* HeapTuple 	 tuple; */
		/* Datum		 values[N_ATTRS]; */
		/* bool		 nulls[N_ATTRS]; */
		/* ProcCtx	*p_state = (ProcCtx *) lfirst(fctx->proc_cursor); */
		/* stack_frame1	*frame = (stack_frame1 *) lfirst(p_state->frame_cursor); */

		/* [> Make and return next tuple to caller <] */
		/* MemSet(values, 0, sizeof(values)); */
		/* MemSet(nulls, 0, sizeof(nulls)); */
		/* values[0] = Int32GetDatum(p_state->proc->pid); */
		/* values[1] = Int32GetDatum(p_state->frame_index); */
		/* values[2] = PointerGetDatum(frame->query); */
		/* values[3] = PointerGetDatum(frame->plan); */
		/* if (p_state->proc->pid == pid) */
			/* nulls[4] = true; */
		/* else */
			/* values[4] = Int32GetDatum(pid); */
		/* tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls); */

		/* [> increment cursor <] */
		/* p_state->frame_cursor = lnext(p_state->frame_cursor); */
		/* p_state->frame_index++; */

		/* if (p_state->frame_cursor == NULL) */
			/* fctx->proc_cursor = lnext(fctx->proc_cursor); */

		/* SRF_RETURN_NEXT(funcctx, HeapTupleGetDatum(tuple)); */
	}
	/* else */
	funcctx = SRF_PERCALL_SETUP();
	SRF_RETURN_DONE(funcctx);

module_not_initilized:
	ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				errmsg("pg_query_state wasn't initialized yet")));
address_to_current_process:
	ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				errmsg("attempt to extract state of current process")));
invalid_backend:
	ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				errmsg("backend with pid=%d not found", pid)));
unrecognized_format:
	ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				errmsg("unrecognized 'format' argument")));
}

/*
 * Execute specific tracing command of other backend with specified 'pid'
 */
static void
exec_trace_cmd(pid_t pid, trace_cmd cmd)
{
	LOCKTAG			tag;
	PGPROC			*proc;

	if (!module_initialized)
		ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("pg_query_state wasn't initialized yet")));

	if (pid == MyProcPid)
		ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					errmsg("attempt to trace self process")));

	proc = BackendPidGetProc(pid);
	if (!proc || proc->backendId == InvalidBackendId)
		ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					errmsg("backend with pid=%d not found", pid)));

	init_lock_tag(&tag, EXECUTOR_TRACE_KEY);
	LockAcquire(&tag, ExclusiveLock, false, false);

	trace_req->tracer = MyProcPid;
	trace_req->traceable = pid;
	trace_req->command = cmd;
	SetLatch(&proc->procLatch);

	/*
	 * Wait until traceable backend handles trace command (resets its pid in shared memory)
	 * so that next 'executor_*' call can not rewrite the shared structure 'trace_req'
	 */
	for (;;)
	{
		/* Check whether traceable backend is reset its pid */
		if (0 == trace_req->traceable)
			break;

		WaitLatch(MyLatch, WL_LATCH_SET, 0);
		CHECK_FOR_INTERRUPTS();
		ResetLatch(MyLatch);
	}

	LockRelease(&tag, ExclusiveLock, false);
}

/*
 * Take a step in tracing of backend with specified pid
 */
PG_FUNCTION_INFO_V1(executor_step);
Datum
executor_step(PG_FUNCTION_ARGS)
{
	pid_t pid = PG_GETARG_INT32(0);

	exec_trace_cmd(pid, STEP);

	PG_RETURN_VOID();
}

/*
 * Continue to execute query under tracing of backend with specified pid
 */
PG_FUNCTION_INFO_V1(executor_continue);
Datum
executor_continue(PG_FUNCTION_ARGS)
{
	pid_t pid = PG_GETARG_INT32(0);

	exec_trace_cmd(pid, CONTINUE);

	PG_RETURN_VOID();
}

/* static void */
/* SendCurrentUserId(void) */
/* { */
	/* SpinLockAcquire(&counterpart_userid->mutex); */
	/* counterpart_userid->userid = GetUserId(); */
	/* SpinLockRelease(&counterpart_userid->mutex); */

	/* SetLatch(counterpart_userid->caller); */
/* } */

/*
 * Extract effective user id from backend on which `proc` points.
 *
 * Assume the `proc` points on valid backend and it's not current process.
 *
 * This fuction must be called after registeration of `UserIdPollReason` and
 * initialization `RemoteUserIdResult` object in shared memory.
 */
/* static Oid */
/* GetRemoteBackendUserId(PGPROC *proc) */
/* { */
	/* Oid result; */

	/* Assert(proc && proc->backendId != InvalidBackendId); */
	/* Assert(UserIdPollReason != INVALID_PROCSIGNAL); */
	/* Assert(counterpart_userid); */

	/* counterpart_userid->userid = InvalidOid; */
	/* counterpart_userid->caller = MyLatch; */
	/* pg_write_barrier(); */

	/* SendProcSignal(proc->pid, UserIdPollReason, proc->backendId); */
	/* for (;;) */
	/* { */
		/* SpinLockAcquire(&counterpart_userid->mutex); */
		/* result = counterpart_userid->userid; */
		/* SpinLockRelease(&counterpart_userid->mutex); */

		/* if (result != InvalidOid) */
			/* break; */

		/* WaitLatch(MyLatch, WL_LATCH_SET, 0); */
		/* CHECK_FOR_INTERRUPTS(); */
		/* ResetLatch(MyLatch); */
	/* } */

	/* return result; */
/* } */

/*
 * Receive a message from a shared message queue until timeout is exceeded.
 *
 * Parameter `*nbytes` is set to the message length and *data to point to the
 * message payload. If timeout is exceeded SHM_MQ_WOULD_BLOCK is returned.
 */
static shm_mq_result
shm_mq_receive_with_timeout(shm_mq_handle *mqh,
							Size *nbytesp,
							void **datap,
							long timeout)
{

#ifdef HAVE_INT64_TIMESTAMP
#define GetNowFloat()	((float8) GetCurrentTimestamp() / 1000.0)
#else
#define GetNowFloat()	1000.0 * GetCurrentTimestamp()
#endif

	float8 	endtime = GetNowFloat() + timeout;
	int 	rc = 0;

	for (;;)
	{
		long 		delay;
		shm_mq_result mq_receive_result;

		mq_receive_result = shm_mq_receive(mqh, nbytesp, datap, true);

		if (mq_receive_result != SHM_MQ_WOULD_BLOCK)
			return mq_receive_result;

		if (rc & WL_TIMEOUT)
			return SHM_MQ_WOULD_BLOCK;

		delay = (long) (endtime - GetNowFloat());
		rc = WaitLatch(MyLatch, WL_LATCH_SET | WL_TIMEOUT, delay);
		CHECK_FOR_INTERRUPTS();
		ResetLatch(MyLatch);
	}
}

/* typedef struct */
/* { */
	/* int		number; */
	/* pid_t	pids[FLEXIBLE_ARRAY_MEMBER]; */
/* } BgWorkerPids; */

/* static void */
/* SendBgWorkerPids(void) */
/* { */
	/* ListCell 		*iter; */
	/* List 			*all_workers = NIL; */
	/* BgWorkerPids 	*msg; */
	/* int				 msg_len; */
	/* int				 i; */
	/* shm_mq_handle 	*mqh; */

	/* mqh = shm_mq_attach(mq, NULL, NULL); */

	/* foreach(iter, QueryDescStack) */
	/* { */
		/* QueryDesc	*curQueryDesc = (QueryDesc *) lfirst(iter); */
		/* List 		*bgworker_pids = NIL; */

		/* extract_running_bgworkers(curQueryDesc->planstate, &bgworker_pids); */
		/* all_workers = list_concat(all_workers, bgworker_pids); */
	/* } */

	/* msg_len = offsetof(BgWorkerPids, pids) */
			/* + sizeof(pid_t) * list_length(all_workers); */
	/* msg = palloc(msg_len); */
	/* msg->number = list_length(all_workers); */
	/* i = 0; */
	/* foreach(iter, all_workers) */
		/* msg->pids[i++] = lfirst_int(iter); */

	/* shm_mq_send(mqh, msg_len, msg, false); */
/* } */

/*
 * Extracts all parallel worker `proc`s running by process `proc`
 */
/* static List * */
/* GetRemoteBackendWorkers(PGPROC *proc) */
/* { */
	/* int				 sig_result; */
	/* shm_mq_handle	*mqh; */
	/* shm_mq_result 	 mq_receive_result; */
	/* BgWorkerPids	*msg; */
	/* Size			 msg_len; */
	/* int				 i; */
	/* List			*result = NIL; */

	/* Assert(proc && proc->backendId != InvalidBackendId); */
	/* Assert(WorkerPollReason != INVALID_PROCSIGNAL); */
	/* Assert(mq); */

	/* mq = shm_mq_create(mq, QUEUE_SIZE); */
	/* shm_mq_set_sender(mq, proc); */
	/* shm_mq_set_receiver(mq, MyProc); */

	/* sig_result = SendProcSignal(proc->pid, WorkerPollReason, proc->backendId); */
	/* if (sig_result == -1) */
		/* return NIL; */

	/* mqh = shm_mq_attach(mq, NULL, NULL); */
	/* mq_receive_result = shm_mq_receive_with_timeout(mqh, &msg_len, (void **) &msg, 1000); */
	/* if (mq_receive_result != SHM_MQ_SUCCESS) */
		/* return NIL; */

	/* for (i = 0; i < msg->number; i++) */
	/* { */
		/* pid_t 	 pid = msg->pids[i]; */
		/* PGPROC	*proc = BackendPidGetProc(pid); */

		/* result = lcons(proc, result); */
	/* } */

	/* shm_mq_detach(mq); */

	/* return result; */
/* } */

/* static shm_mq_msg * */
/* copy_msg(shm_mq_msg *msg) */
/* { */
	/* shm_mq_msg *result = palloc(msg->length); */

	/* memcpy(result, msg, msg->length); */
	/* return result; */
/* } */

typedef struct
{
	pgqsResultCode result;
	int		 warnings;				/* bitmap of warnings */
	int		 npworkers;
	PGPROC	*pworkers[FLEXIBLE_ARRAY_MEMBER];
} pgqsPreambleMsg;

typedef struct
{
	Size	 length;
	int		 nframes;
	char	 stack[FLEXIBLE_ARRAY_MEMBER];
} pgqsStackMsg;

static pgqsResultCode
GetRemoteBackendQueryState(PGPROC *proc,
						   bool verbose,
						   bool costs,
						   bool timing,
						   bool buffers,
						   bool triggers,
						   ExplainFormat format,
						   List	**result,
						   int *warnings)
{
	List		*procs;
	int		 	 sig_result;

	Assert(QueryStatePollReason != INVALID_PROCSIGNAL);
	Assert(mq);

	/* fill in parameters for query state request */
	params->userid = GetUserId();
	params->verbose = verbose;
	params->costs = costs;
	params->timing = timing;
	params->buffers = buffers;
	params->triggers = triggers;
	params->format = format;
	pg_write_barrier();

	/* send signal `QueryStatePollReason` to `proc` */
	sig_result = SendProcSignal(proc->pid,
								QueryStatePollReason,
								proc->backendId);
	if (sig_result == -1)
	{
		if (errno == ESRCH)
			return BACKEND_DIED;
		goto signal_error;
	}

	procs = list_make1(proc);
	while (list_length(procs) > 0)
	{
		PGPROC 			*cur_proc = (PGPROC *) linitial(procs);
		shm_mq_handle  	*mqh;
		shm_mq_result	 mq_receive_result;
		pgqsPreambleMsg	*preamble;
		pgqsStackMsg	*stack_msg;
		Size			 len;
		int				 i;
		ProcState		*proc_state;
		StackFrame		*qs_stack;

		mq = shm_mq_create(mq, QUEUE_SIZE);
		shm_mq_set_sender(mq, proc);
		shm_mq_set_receiver(mq, MyProc); 	/* this function notifies the
											   counterpart to come into data
											   transfer */

		/* retrieve result data from message queue */
		mqh = shm_mq_attach(mq, NULL, NULL);
		mq_receive_result = shm_mq_receive_with_timeout(mqh,
														&len,
														(void **) &preamble,
														5000);
		if (mq_receive_result != SHM_MQ_SUCCESS)
			continue;

		if (cur_proc == proc && preamble->result != QS_RETURNED)
			return preamble->result;

		*warnings = preamble->warnings;
		for (i = 0; i < preamble->npworkers; i++)
			procs = lappend(procs, preamble->pworkers[i]);

		mq_receive_result = shm_mq_receive(mqh,
										   &len,
										   (void **) &stack_msg,
										   false);
		Assert(mq_receive_result == SHM_MQ_SUCCESS);
		Assert(stack_msg->length == len);

		proc_state = palloc(sizeof(ProcState));
		proc_state->proc = cur_proc;
		proc_state->frames = deserialize_stack(stack_msg->stack,
											   stack_msg->length);
		*result = lappend(*result, proc_state);

		procs = list_delete_first(procs);
	}


	/*
	 * collect results from all alived processes
	 */
	/* foreach(iter, alive_procs) */
	/* { */
		/* PGPROC 			*proc = (PGPROC *) lfirst(iter); */

		/* [> prepare message queue to transfer data <] */
		/* mq = shm_mq_create(mq, QUEUE_SIZE); */
		/* shm_mq_set_sender(mq, proc); */
		/* shm_mq_set_receiver(mq, MyProc); */	/* this function notifies the */
											   /* counterpart to come into data */
											   /* transfer */

		/* [> retrieve result data from message queue <] */
		/* mqh = shm_mq_attach(mq, NULL, NULL); */
		/* mq_receive_result = shm_mq_receive_with_timeout(mqh, */
														/* &len, */
														/* (void **) &msg, */
														/* 5000); */
		/* if (mq_receive_result != SHM_MQ_SUCCESS) */
			/* [> counterpart is died, not consider it <] */
			/* continue; */

		/* Assert(len == msg->length); */

		/* [> aggregate result data <] */
		/* result = lappend(result, copy_msg(msg)); */

		/* shm_mq_detach(mq); */
	/* } */

	return QS_RETURNED;

signal_error:
	ereport(ERROR, (errcode(ERRCODE_INTERNAL_ERROR),
				errmsg("invalid send signal")));
}

/*
 *	Get List of `stack_frame`s as a stack of function calls starting from
 *	outermost call. Each entry contains query text and query state in form of
 *	EXPLAIN ANALYZE output.
 *
 *	Assume extension is enabled and QueryDescStack is not empty
 */
static List *
runtime_explain()
{
	ExplainState    *es;
	ListCell	    *i;
	List			*result = NIL;

	Assert(list_length(QueryDescStack) > 0);

	/* initialize explain state with all config parameters */
	es = NewExplainState();
	es->analyze = true;
	es->verbose = params->verbose;
	es->costs = params->costs;
	es->buffers = params->buffers && pg_qs_buffers;
	es->timing = params->timing && pg_qs_timing;
	es->summary = false;
	es->format = params->format;
	es->runtime = true;

	/* collect query state outputs of each plan entry of stack */
	foreach(i, QueryDescStack)
	{
		QueryDesc 	*currentQueryDesc = (QueryDesc *) lfirst(i);
		StackFrame	*qs_frame = palloc(sizeof(StackFrame));

		/* save query text */
		qs_frame->query = currentQueryDesc->sourceText;

		/* save plan with statistics */
		initStringInfo(es->str);
		ExplainBeginOutput(es);
		ExplainPrintPlan(es, currentQueryDesc);
		if (params->triggers)
			ExplainPrintTriggers(es, currentQueryDesc);
		ExplainEndOutput(es);

		/* Remove last line break */
		if (es->str->len > 0 && es->str->data[es->str->len - 1] == '\n')
			es->str->data[--es->str->len] = '\0';

		/* Fix JSON to output an object */
		if (params->format == EXPLAIN_FORMAT_JSON)
		{
			es->str->data[0] = '{';
			es->str->data[es->str->len - 1] = '}';
		}

		qs_frame->plan = es->str->data;

		result = lcons(qs_frame, result);
	}

	return result;
}

/*
 * Compute length of serialized stack frame
 */
static int
serialized_stack_frame_length(StackFrame *qs_frame)
{
	return 	INTALIGN(strlen(qs_frame->query) + VARHDRSZ)
		+ 	INTALIGN(strlen(qs_frame->plan) + VARHDRSZ);
}

/*
 * Compute overall length of serialized stack of function calls
 */
static int
serialized_stack_length(List *qs_stack)
{
	ListCell 	*i;
	int			result = 0;

	foreach(i, qs_stack)
	{
		StackFrame *qs_frame = (StackFrame *) lfirst(i);

		result += serialized_stack_frame_length(qs_frame);
	}

	return result;
}

/*
 * Convert StackFrame record into serialized text format version
 * 		Increment '*dest' pointer to the next serialized stack frame
 */
static void
serialize_stack_frame(char **dest, StackFrame *qs_frame)
{
	SET_VARSIZE(*dest, strlen(qs_frame->query) + VARHDRSZ);
	memcpy(VARDATA(*dest), qs_frame->query, strlen(qs_frame->query));
	*dest += INTALIGN(VARSIZE(*dest));

	SET_VARSIZE(*dest, strlen(qs_frame->plan) + VARHDRSZ);
	memcpy(VARDATA(*dest), qs_frame->plan, strlen(qs_frame->plan));
	*dest += INTALIGN(VARSIZE(*dest));
}

/*
 * Convert List of StackFrame records into serialized structures laid out sequentially
 */
static void
serialize_stack(char *dest, List *qs_stack)
{
	ListCell		*i;

	foreach(i, qs_stack)
	{
		StackFrame *qs_frame = (StackFrame *) lfirst(i);

		serialize_stack_frame(&dest, qs_frame);
	}
}

/*
 * Extract to *result all handlers of parallel workers running from leader
 * process that executes plan tree whose state's root is `node`.
 */
static bool
extract_pworkers(PlanState *node, List **result)
{
	if (node == NULL)
		return false;

	if (IsA(node, GatherState))
	{
		GatherState *gather_node = (GatherState *) node;

		if (gather_node->pei)
		{
			int i;

			for (i = 0; i < gather_node->pei->pcxt->nworkers_launched; i++)
			{
				BackgroundWorkerHandle 	*bgwh;

				bgwh = gather_node->pei->pcxt->worker[i].bgwhandle;
				if (bgwh)
					*result = lcons(bgwh, *result);
			}
		}
	}
	return planstate_tree_walker(node, extract_pworkers, (void *) result);
}

static void
mq_wait_turn()
{
	/* wait until caller sets this process as sender to message queue */
	for (;;)
	{
		if (shm_mq_get_sender(mq) == MyProc)
			break;

		WaitLatch(MyLatch, WL_LATCH_SET, 0);
		CHECK_FOR_INTERRUPTS();
		ResetLatch(MyLatch);
	}
}

/*
 * Send state of current query to shared queue.
 * This function is called when fire custom signal QueryStatePollReason
 */
void
SendQueryState(void)
{
	shm_mq_handle 	*mqh;
	List			*all_pworkers;
	List			*alived_pworkers;
	ListCell		*iter;
	pgqsPreambleMsg	*preamble;
	pgqsStackMsg	*stack_msg;
	Size			 msg_len;
	List			*qs_stack;
	int				 i;

	/* check if module is enabled */
	if (!pg_qs_enable)
	{
		pgqsPreambleMsg msg;

		msg_len = offsetof(pgqsPreambleMsg, warnings);
		msg = (pgqsPreambleMsg) { STAT_DISABLED };

		mq_wait_turn();
		mqh = shm_mq_attach(mq, NULL, NULL);
		shm_mq_send(mqh, msg_len, &msg, false);
		return;
	}

	/* check if backend doesn't execute any query */
	else if (list_length(QueryDescStack) == 0)
	{
		pgqsPreambleMsg msg;

		msg_len = offsetof(pgqsPreambleMsg, warnings);
		msg = (pgqsPreambleMsg) { QUERY_NOT_RUNNING };

		mq_wait_turn();
		mqh = shm_mq_attach(mq, NULL, NULL);
		shm_mq_send(mqh, msg_len, &msg, false);
		return;
	}

	/* happy path */
	extract_pworkers(((QueryDesc *) llast(QueryDescStack))->planstate,
					 &all_pworkers);
	alived_pworkers = NIL;
	foreach(iter, all_pworkers)
	{
		pid_t	 pid;
		PGPROC	*proc;
		BackgroundWorkerHandle *bgwh = (BackgroundWorkerHandle *) lfirst(iter);
		BgwHandleStatus			status;
		int		 sig_result;

		status = GetBackgroundWorkerPid(bgwh, &pid);
		if (status != BGWH_STARTED)
			continue;

		proc = BackendPidGetProc(pid);
		sig_result = SendProcSignal(pid,
									QueryStatePollReason,
									proc->backendId);
		if (sig_result == -1)
		{
			if (errno != ESRCH)
				goto signal_error;
			continue;
		}

		alived_pworkers = lappend(alived_pworkers, proc);
	}

	msg_len = offsetof(pgqsPreambleMsg, pworkers)
				+ INTALIGN(sizeof(PGPROC *)) * list_length(alived_pworkers);
	preamble = palloc(msg_len);
	preamble->result = QS_RETURNED;
	preamble->warnings = 0;
	if (params->timing && !pg_qs_timing)
		preamble->warnings |= TIMINIG_OFF_WARNING;
	if (params->buffers && !pg_qs_buffers)
		preamble->warnings |= BUFFERS_OFF_WARNING;
	preamble->npworkers = list_length(alived_pworkers);
	i = 0;
	foreach(iter, alived_pworkers)
	{
		PGPROC *proc = (PGPROC *) lfirst(iter);

		preamble->pworkers[i++] = proc;
	}

	mq_wait_turn();
	mqh = shm_mq_attach(mq, NULL, NULL);
	shm_mq_send(mqh, msg_len, preamble, false);

	qs_stack = runtime_explain();
	msg_len = serialized_stack_length(qs_stack);
	stack_msg = palloc(msg_len);
	stack_msg->length = msg_len;
	stack_msg->nframes = list_length(qs_stack);
	serialize_stack(stack_msg->stack, qs_stack);
	shm_mq_send(mqh, msg_len, stack_msg, false);

signal_error:
	ereport(ERROR, (errcode(ERRCODE_INTERNAL_ERROR),
				errmsg("invalid send signal")));
}
