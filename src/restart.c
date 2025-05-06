#include "inline.h"
#include "inlineheap.h"
#include "inlinequeue.h"



#include "restart.h"
#include "backtrack.h"
#include "bump.h"
#include "decide.h"
#include "internal.h"
#include "kimits.h"
#include "logging.h"
#include "print.h"
#include "reluctant.h"
#include "report.h"




#include <inttypes.h>

bool kissat_restarting (kissat *solver) {
  assert (solver->unassigned);
  if (!GET_OPTION (restart))
    return false;
  if (!solver->level)
    return false;
  if (CONFLICTS < solver->limits.restart.conflicts)
    return false;
  if (solver->stable)
    return kissat_reluctant_triggered (&solver->reluctant);
  const double fast = AVERAGE (fast_glue);
  const double slow = AVERAGE (slow_glue);
  const double margin = (100.0 + GET_OPTION (restartmargin)) / 100.0;
  const double limit = margin * slow;
  kissat_extremely_verbose (solver,
                            "restart glue limit %g = "
                            "%.02f * %g (slow glue) %c %g (fast glue)",
                            limit, margin, slow,
                            (limit > fast    ? '>'
                             : limit == fast ? '='
                                             : '<'),
                            fast);
  return (limit <= fast);
}

void kissat_update_focused_restart_limit (kissat *solver) {
  assert (!solver->stable);
  limits *limits = &solver->limits;
  uint64_t restarts = solver->statistics.restarts;
  uint64_t delta = GET_OPTION (restartint);
  if (restarts)
    delta += kissat_logn (restarts) - 1;
  limits->restart.conflicts = CONFLICTS + delta;
  kissat_extremely_verbose (solver,
                            "focused restart limit at %" PRIu64
                            " after %" PRIu64 " conflicts ",
                            limits->restart.conflicts, delta);
}

static unsigned reuse_stable_trail (kissat *solver) {
  const heap *const scores = SCORES;
  const unsigned next_idx = kissat_next_decision_variable (solver);
  const double limit = kissat_get_heap_score (scores, next_idx);
  unsigned level = solver->level, res = 0;
  while (res < level) {
    frame *f = &FRAME (res + 1);
    const unsigned idx = IDX (f->decision);
    const double score = kissat_get_heap_score (scores, idx);
    if (score <= limit)
      break;
    res++;
  }
  return res;
}

static unsigned reuse_focused_trail (kissat *solver) {
  const links *const links = solver->links;
  const unsigned next_idx = kissat_next_decision_variable (solver);
  const unsigned limit = links[next_idx].stamp;
  LOG ("next decision variable stamp %u", limit);
  unsigned level = solver->level, res = 0;
  while (res < level) {
    frame *f = &FRAME (res + 1);
    const unsigned idx = IDX (f->decision);
    const unsigned score = links[idx].stamp;
    if (score <= limit)
      break;
    res++;
  }
  return res;
}

static unsigned reuse_trail (kissat *solver) {
  assert (solver->level);
  assert (!EMPTY_STACK (solver->trail));

  if (!GET_OPTION (restartreusetrail))
    return 0;

  unsigned res;

  if (solver->stable)
    res = reuse_stable_trail (solver);
  else
    res = reuse_focused_trail (solver);

  LOG ("matching trail level %u", res);

  if (res) {
    INC (restarts_reused_trails);
    ADD (restarts_reused_levels, res);
    LOG ("restart reuses trail at decision level %u", res);
  } else
    LOG ("restarts does not reuse the trail");

  return res;
}

void kissat_restart (kissat *solver) {
  START (restart);
  INC (restarts);
  ADD (restarts_levels, solver->level);
  if (solver->stable)
    INC (stable_restarts);
  else
    INC (focused_restarts);

  //---------------------------------------
  if (   (CONFLICTS < 20000) && ((solver->statistics.restarts) % 10)  && (solver->stable) )
  {
  
	  kissat_inverDeduce (solver);
  }
  //---------------------------------------

  unsigned level = reuse_trail (solver);
  kissat_extremely_verbose (solver,
                            "restarting after %" PRIu64 " conflicts"
                            " (limit %" PRIu64 ")",
                            CONFLICTS, solver->limits.restart.conflicts);
  LOG ("restarting to level %u", level);
  kissat_backtrack_in_consistent_state (solver, level);
  if (!solver->stable)
    kissat_update_focused_restart_limit (solver);
  REPORT (1, 'R');
  STOP (restart);
}

void kissat_inverDeduce (struct kissat * solver)
{
  assigned *const assigned = solver->assigned;
  value *const values = solver->values;
  ward *const arena = BEGIN_STACK (solver->arena);
  
  unsigned *trail = BEGIN_ARRAY (solver->trail);
  unsigned *new_end = trail; 
  unsigned *old_end = END_ARRAY (solver->trail);
  unsigned *q = new_end;




  for (const unsigned *p = q; p != old_end; p++) 
  {
	  //µ±Ç°ÎÄ×Ö
      const unsigned lit = *p;
	  const unsigned not_lit = NOT (lit);

      const unsigned idx = IDX (lit);
      assert (idx < VARS);
	  assert (values [lit] > 0);

      flags *f = FLAGS (idx);
	  f->isleaf = true;

      struct assigned *a = assigned + idx;

	  if (a->binary) {
		const unsigned other = a->reason;

	    unsigned  idx_other = IDX (other);
		flags *f_other = FLAGS (idx_other);
	    f_other->isleaf = false;
	  
	  } else {

	    const reference ref = a->reason;
	    assert (ref < SIZE_STACK (solver->arena));
      
	    if (ref == DECISION_REASON)
		  continue;

	    if (ref == UNIT_REASON)
		  continue;
		
		clause *c = (clause *) (arena + ref);
	    assert((c->size) > 1);

		assert (kissat_clause_in_arena (solver, c));
		
		for (all_literals_in_clause (other, c))
		{
		  if (other != lit) {
			assert (other != not_lit);

			unsigned  idx_other = IDX (other);
		    flags *f_other = FLAGS (idx_other);
	        f_other->isleaf = false;
		  }
		}

	  } 
      
  } 

  assert (EMPTY_STACK (solver->promote));  

  for (const unsigned *p = q; p != old_end; p++) 
  {
      const unsigned lit = *p;
      const unsigned idx = IDX (lit);

      flags *f = FLAGS (idx);
	  if (f->isleaf)
	  {
		  PUSH_STACK (solver->promote, lit);
	  }
  }

  for (all_stack (unsigned, lit, solver->promote)) 
  {	  	  
	  const unsigned idx = IDX (lit);	  
	  kissat_bump_variable (solver, idx);	  
  }
  CLEAR_STACK (solver->promote);
  
}