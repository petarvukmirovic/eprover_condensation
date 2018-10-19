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

/*-----------------------------------------------------------------------
//
// Function: do_condense_lin()
//
//   Implementation of condensation that uses number of subsumption calls
//   equal to at most the number of literals in the original clause.
//   This algorithm is a version of
//   https://www.researchgate.net/publication/220547401_Removing_Redundancy_from_a_Clause
//   changed to deal with equality efficiently.
//
// Global Variables:
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

static bool do_condense_lin(Clause_p cl)
{
   ClauseSubsumeOrderSortLits(cl);

   Clause_p orig = ClauseFlatCopy(cl);
   Clause_p dbg_cpy = ClauseFlatCopy(orig);
   PStack_p lits = ClauseToStack(cl);
   bool condensed = false;

   while(!PStackEmpty(lits))
   {
      Eqn_p lit = PStackPopP(lits);
      EqnSetProp(lit, EPIsCondensed);
      
      if(ClauseSubsumesClauseModuloSetEq(orig, cl))
      {
         ClauseRemoveLiteral(cl, lit);
         condensed = true;
      }
      else
      {
         EqnDelProp(lit, EPIsCondensed);
      }
   }

   Condense(dbg_cpy);
   if(ClauseLiteralNumber(dbg_cpy) != ClauseLiteralNumber(cl))
   {
      fprintf(stderr, "# orig: ");
      EqnListPrint(stderr, orig->literals, "|", false, true);
      fprintf(stderr, "\n# orig condense: ");
      EqnListPrint(stderr, dbg_cpy->literals, "|", false, true);
      fprintf(stderr, "\n# new condense: ");
      EqnListPrint(stderr, cl->literals, "|", false, true);
      fprintf(stderr, "\n");
   }

   PStackFree(lits);
   ClauseFree(orig);    

   return condensed;
}

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
            if(swap == true)
            {
               Error("SWAP = TRUE", SYNTAX_ERROR);
            }
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

   if((clause->pos_lit_no > 1) || (clause->neg_lit_no >1))
   {
      res = CondenseOnceSet(clause);
      if(res)
      {
         CondensationSuccesses++;
         DocClauseModificationDefault(clause, inf_condense, NULL);
         ClausePushDerivation(clause, DCCondense, NULL, NULL);
      }
   }
   
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
