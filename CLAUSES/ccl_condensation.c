/*-----------------------------------------------------------------------

File  : ccl_condensation.c

Author: Stephan Schulz (schulz@eprover.org)

Contents

  Implementation of the condensation rule.

  Copyright 2012 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1>     New

-----------------------------------------------------------------------*/

#include "ccl_condensation.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

long CondensationAttempts = 0;
long CondensationSuccesses = 0;

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/


/*-----------------------------------------------------------------------
//
// Function: CondenseOnce()
//
//   Try to condense clause. If successful, simplify the clause, and
//   return true. If not, the clause is unchanged and false is
//   returned.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

bool CondenseOnce(Clause_p clause)
{
   Eqn_p    l1, l2, newlits;
   Subst_p  subst = SubstAlloc();
   Clause_p cand;
   bool     swap;

   assert(ClauseIsSubsumeOrdered(clause));

   for(l1=clause->literals; l1; l1=l1->next)
   {
      assert(l1);
      for(l2=l1->next; l2; l2=l2->next)
      {
         for(swap = false; !swap; swap = true)
         {
            if(LiteralUnifyOneWay(l1, l2, subst, swap))
            {
               newlits = EqnListCopyExcept(clause->literals, l2, l1->bank);
               SubstBacktrack(subst);
               EqnListRemoveDuplicates(newlits);
               EqnListRemoveResolved(&newlits);
               cand = ClauseAlloc(newlits);
               cand->weight = ClauseStandardWeight(cand);
               ClauseSubsumeOrderSortLits(cand);
               if(ClauseSubsumesClause(cand, clause))
               {
                  EqnListFree(clause->literals);
                  clause->literals = cand->literals;
                  ClauseRecomputeLitCounts(clause);
                  clause->weight = ClauseStandardWeight(clause);
                  cand->literals = NULL;
                  ClauseFree(cand);
                  SubstFree(subst);

                  return true;
               }
               else
               {
                  ClauseFree(cand);
               }
            }
         }
      }
   }
   SubstFree(subst);
   return false;
}

bool CondenseOnceSet(Clause_p clause)
{
   Eqn_p    l1, l2, newlits;
   Subst_p  subst = SubstAlloc();
   Clause_p cand;
   int      swap;
 
   assert(ClauseIsSubsumeOrdered(clause));

   for(l1=clause->literals; l1; l1=l1->next)
   {
      assert(l1);
      for(l2=EqnIsNegative(l1) ? l1 : l1->next; l2; l2=l2->next)
      {
         for(swap = (l2 == l1) ? 1 : 0; swap < 2; swap++)
         {
            if((l2 != l1 && LiteralUnifyOneWay(l1, l2, subst, swap == 1 ? true : false)) ||
               (l2 == l1 && EqnUnifySides(l1, subst)))
            {
               newlits = EqnListCopyExcept(clause->literals, l2, l1->bank);
               SubstBacktrack(subst);
               EqnListRemoveDuplicates(newlits);
               EqnListRemoveResolved(&newlits);
               cand = ClauseAlloc(newlits);
               cand->weight = ClauseStandardWeight(cand);
               ClauseSubsumeOrderSortLits(cand);
               if(ClauseSubsumesClauseModuloSet(cand, clause))
               {
                  EqnListFree(clause->literals);
                  clause->literals = cand->literals;
                  ClauseRecomputeLitCounts(clause);
                  clause->weight = ClauseStandardWeight(clause);
                  cand->literals = NULL;
                  ClauseFree(cand);
                  SubstFree(subst);

                  return true;
               }
               else
               {
                  ClauseFree(cand);
               }
            }
         }
      }
   }
   SubstFree(subst);
   return false;
}


/*-----------------------------------------------------------------------
//
// Function: CondenseSet()
//
//   Condense a clause as much as possible. Return true if the clause
//   was changed, false otherwise. Implementation that is supposed to
//   be faster than Condense() -- see do_condense_lin;
//
// Global Variables:
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

bool CondenseSet(Clause_p clause)
{
   bool res = false;

   CondensationAttempts++;

#ifndef NDEBUG
   Clause_p orig = ClauseFlatCopy(clause);
   Clause_p dbg_cpy = ClauseFlatCopy(clause);
#endif

   if((clause->pos_lit_no > 1) || (clause->neg_lit_no >1))
   {
      clause->weight = ClauseStandardWeight(clause);
      ClauseSubsumeOrderSortLits(clause);

      while(CondenseOnceSet(clause))
      {
         /*fprintf(stderr, "\n# condensed once : ");
         EqnListPrint(stderr, clause->literals, "|", false, true);*/

         res = true;
      }

      if(res)
      {
         CondensationSuccesses++;
         DocClauseModificationDefault(clause, inf_condense, NULL);
         ClausePushDerivation(clause, DCCondense, NULL, NULL);
      }
   }

#ifndef NDEBUG
   Condense(dbg_cpy);
   /*if(ClauseLiteralNumber(dbg_cpy) != ClauseLiteralNumber(clause))
   {
      fprintf(stderr, "#orig (%d / %d): ", ClauseLiteralNumber(dbg_cpy), ClauseLiteralNumber(clause));
      EqnListPrint(stderr, orig->literals, "|", false, true);
      fprintf(stderr, "\n#old condense: ");
      EqnListPrint(stderr, dbg_cpy->literals, "|", false, true);
      fprintf(stderr, "\n#new condense: ");
      EqnListPrint(stderr, clause->literals, "|", false, true);
      fprintf(stderr, "\n");
   }*/
   assert(ClauseLiteralNumber(dbg_cpy) >= ClauseLiteralNumber(clause));
   ClauseFree(orig);
   ClauseFree(dbg_cpy);
#endif
   
   return res;
}

/*-----------------------------------------------------------------------
//
// Function: Condense()
//
//   Condense a clause as much as possible. Return true if the clause
//   was changed, false otherwise.
//
// Global Variables:
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

bool Condense(Clause_p clause)
{
   bool res = false;

   CondensationAttempts++;

   /*fprintf(stderr, "# orig : ");
   EqnListPrint(stderr, clause->literals, "|", false, true);*/

   if((clause->pos_lit_no > 1) || (clause->neg_lit_no >1))
   {
      clause->weight = ClauseStandardWeight(clause);
      ClauseSubsumeOrderSortLits(clause);

      while(CondenseOnce(clause))
      {
         /*fprintf(stderr, "\n# condensed once : ");
         EqnListPrint(stderr, clause->literals, "|", false, true);*/

         res = true;
      }

      if(res)
      {
         CondensationSuccesses++;
         DocClauseModificationDefault(clause, inf_condense, NULL);
         ClausePushDerivation(clause, DCCondense, NULL, NULL);
      }
   }
   return res;
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
