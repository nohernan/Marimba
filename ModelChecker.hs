    -- Marimba is a model checker for HMMs whose specification language is the logic POCTL*
    -- Copyright (C) 2014  Noe Hernandez	

    -- This file is part of Marimba.

    -- Marimba is free software: you can redistribute it and/or modify
    -- it under the terms of the GNU General Public License as published by
    -- the Free Software Foundation, either version 3 of the License, or
    -- (at your option) any later version.

    -- Marimba is distributed in the hope that it will be useful,
    -- but WITHOUT ANY WARRANTY; without even the implied warranty of
    -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    -- GNU General Public License for more details.

    -- You should have received a copy of the GNU General Public License
    -- along with Marimba. If not, see <http://www.gnu.org/licenses/>.

module ModelChecker where

import DirectApproach
import Courcoubetis
import Data.Array

----------------------------------------------------
----------------------------------------------------
-- Example:
-- satPOCTL myHMM (Prob "<" 0.1 (NextPath [2] (NoPath (FormP (AtomP "q")))))
-- [2]
-- satPOCTL myHMM (Prob ">" 0.02 (NextPath [1] (NextPath [2] (NextPath [1] (FormP VerdadP)))))
-- [2]
-- where myHMM is defined in the file DirectApproach.hs
satPOCTL :: HMM -> POCTL -> [Int]
satPOCTL hmm VerdadP	= elems (statesHMM hmm)
satPOCTL _   FalsoP	= []
satPOCTL hmm (AtomP s) 	= [ (statesHMM hmm)!ind | ind<-indices lab, elem s (lab!ind)]
      where                                        
        lab = labelFHMM hmm 
satPOCTL hmm (NoP p)	= satPOCTL newHmm ap    
      where                                        
        (newHmm,_)  = extHMM hmm (NoP p) 0						
        (ap,_)      = rename (NoP p) 0
satPOCTL hmm (OP p1 p2)	= satPOCTL newHmm ap 
      where				
        (newHmm, _) = extHMM hmm (OP p1 p2) 0								
        (ap, _)     = rename (OP p1 p2) 0
satPOCTL hmm (YP p1 p2)	= satPOCTL newHmm ap 
	where						
          (newHmm, _) = extHMM hmm (YP p1 p2) 0								
          (ap, _)     = rename (YP p1 p2) 0
satPOCTL hmm (Prob c f path) = satPOCTL newHmm ap	                                                
        where								
          (newHmm, _) = extHMM hmm (Prob c f path) 0						
          (ap, _)     = rename (Prob c f path) 0

----------------------------------------------------
----------------------------------------------------
-- It returns the extended HMM with the updated labelling function
-- Example:
--
-- extHMM myHMM (NoP (OP (AtomP "p") (NoP (AtomP "q")))) 0
-- (HMM {statesHMM = array (1,2) [(1,1),(2,2)], 
--   pTransHMM = array ((1,1),(2,2)) [((1,1),0.7),((1,2),0.3),((2,1),0.4),((2,2),0.6)], 
--   labelFHMM = array (1,2) [(1,["p","ap0","ap1"]),(2,["q","ap2"])], obsHMM = [1, 2, 3], 
--   pObsHMM = array ((1,1),(2,3)) [((1,1),0.1),((1,2),0.4),((1,3),0.5),((2,1),0.7),((2,2),0.2),((2,3),0.1)], 
--   initDiHMM = array (1,2) [(1,0.6),(2,0.4)]}, 3)          
extHMM :: HMM -> POCTL -> Int -> (HMM, Int)
extHMM hmm VerdadP i 	= (hmm, i)
extHMM hmm FalsoP  i	= (hmm, i)
extHMM hmm (AtomP s) i  = (hmm, i)
extHMM hmm (NoP p) i 	= case newP of 
                VerdadP -> (HMM {statesHMM = statesHMM hmm, 
                                 pTransHMM = pTransHMM hmm, 
                                 labelFHMM = lab, 
                                 obsHMM = obsHMM hmm,	
                                 pObsHMM = pObsHMM hmm, 
                                 initDiHMM = initDiHMM hmm}, 
                         j+1)
                FalsoP  -> (HMM {statesHMM = statesHMM hmm, 
                                 pTransHMM = pTransHMM hmm,
                                 labelFHMM = listArray (bounds lab) [ (lab!k)++["ap"++show j] | k<-indices lab], 
                                 obsHMM = obsHMM hmm,			                             
                                 pObsHMM = pObsHMM hmm, 
                                 initDiHMM = initDiHMM hmm}, 
                         j+1)
                AtomP s -> (HMM {statesHMM = statesHMM hmm, 
                                 pTransHMM = pTransHMM hmm, 
                                 labelFHMM = listArray (bounds lab) [ if (not (elem s (lab!k)))
                                                        then (lab!k)++["ap"++show j]
                                                        else (lab!k) | k<-indices lab], 
                                 obsHMM = obsHMM hmm,	
                                 pObsHMM = pObsHMM hmm, 
                                 initDiHMM = initDiHMM hmm}, 
                         j+1)
        where
                 lab            = labelFHMM newHMM
                 (newHMM,j)     = extHMM hmm p i
                 (newP, _)	= rename p i
extHMM hmm (OP p1 p2) i = case newP1 of 
                        VerdadP -> (HMM {statesHMM = statesHMM hmm, 
                                         pTransHMM = pTransHMM hmm, 
                                         labelFHMM = listArray (bounds lab) [ (lab!k)++["ap"++show l] | k<-indices lab], 
                                         obsHMM = obsHMM hmm,
                                         pObsHMM = pObsHMM hmm, 
                                         initDiHMM = initDiHMM hmm}, 
                                    l+1) 
                        FalsoP  -> case newP2 of
                                VerdadP -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = listArray (bounds lab) [ (lab!k)++["ap"++show l] | k<-indices lab], 
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm},
                                            l+1) 
                                FalsoP  -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = lab,
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1) 
                                AtomP s  -> (HMM {statesHMM = statesHMM hmm, 
                                                  pTransHMM = pTransHMM hmm, 
                                                  labelFHMM = listArray (bounds lab)
                                                        [ if elem s (lab!k)
                                                                then (lab!k)++["ap"++show l]
                                                                else (lab!k) | k<-indices lab], 
                                                  obsHMM = obsHMM hmm,
                                                  pObsHMM = pObsHMM hmm, 
                                                  initDiHMM = initDiHMM hmm}, 
                                            l+1) 
                        AtomP s  -> case newP2 of
                                VerdadP -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = listArray (bounds lab) [ (lab!k)++["ap"++show l] | k<-indices lab], 
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1)                 
                                FalsoP  -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = listArray (bounds lab) 
                                                             [ if elem s (lab!k)
                                                                then (lab!k)++["ap"++show l]
                                                                else (lab!k) | k<-indices lab], 
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1)    
                                AtomP ss->  (HMM {statesHMM = statesHMM hmm, 
                                                  pTransHMM = pTransHMM hmm,
                                        	  labelFHMM = listArray (bounds lab) 
                                                                [ if elem s (lab!k) || elem ss (lab!k)
                                                                        then (lab!k)++["ap"++show l]
                                                                        else (lab!k) | k<-indices lab], 
                                                  obsHMM = obsHMM hmm,
                                                  pObsHMM = pObsHMM hmm, 
                                                  initDiHMM = initDiHMM hmm}, 
                                            l+1)
                        where
                          lab 	      = labelFHMM newHMM
                          (tmpHMM, j) = extHMM hmm    p1 i 
                          (newHMM, l) = extHMM tmpHMM p2 j
                          (newP1, jj) = rename p1 i
                          (newP2, _ ) = rename p2 jj

extHMM hmm (YP p1 p2) i = case newP1 of 
                        FalsoP ->  (HMM {statesHMM = statesHMM hmm, 
                                         pTransHMM = pTransHMM hmm, 
                                         labelFHMM = lab,
                                         obsHMM = obsHMM hmm,
                                         pObsHMM = pObsHMM hmm, 
                                         initDiHMM = initDiHMM hmm}, 
                                    l+1)
                        VerdadP -> case newP2 of
                                VerdadP -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = listArray (bounds lab) [ (lab!k)++["ap"++show l] | k<-indices lab], 
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm},
                                            l+1) 
                                FalsoP  -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = lab,
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1) 
                                AtomP s  -> (HMM {statesHMM = statesHMM hmm, 
                                                  pTransHMM = pTransHMM hmm, 
                                                  labelFHMM = listArray (bounds lab)
                                                              [ if elem s (lab!k)
                                                                then (lab!k)++["ap"++show l]
                                                                else (lab!k) | k<-indices lab], 
                                                  obsHMM = obsHMM hmm,
                                                  pObsHMM = pObsHMM hmm, 
                                                  initDiHMM = initDiHMM hmm}, 
                                            l+1) 
                        AtomP s  -> case newP2 of
                                VerdadP ->  (HMM {statesHMM = statesHMM hmm, 
                                                  pTransHMM = pTransHMM hmm, 
                                                  labelFHMM = listArray (bounds lab)
                                                              [ if elem s (lab!k)
                                                                then (lab!k)++["ap"++show l]
                                                                else (lab!k) | k<-indices lab], 
                                                  obsHMM = obsHMM hmm,
                                                  pObsHMM = pObsHMM hmm, 
                                                  initDiHMM = initDiHMM hmm}, 
                                            l+1)                
                                FalsoP  -> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm, 
                                                 labelFHMM = lab,
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1) 
                                AtomP ss-> (HMM {statesHMM = statesHMM hmm, 
                                                 pTransHMM = pTransHMM hmm,
                                        	 labelFHMM = listArray (bounds lab) 
                                                                [ if elem s (lab!k) && elem ss (lab!k)
                                                                  then (lab!k)++["ap"++show l]
                                                                  else (lab!k) | k<-indices lab], 
                                                 obsHMM = obsHMM hmm,
                                                 pObsHMM = pObsHMM hmm, 
                                                 initDiHMM = initDiHMM hmm}, 
                                            l+1)
                        where
                          lab 	= labelFHMM newHMM
                          (tmpHMM, j) = extHMM hmm    p1 i 
                          (newHMM, l) = extHMM tmpHMM p2 j
                          (newP1, jj) = rename p1 i
                          (newP2, _ ) = rename p2 jj
-- Notice that path is not a POCTL* formula, so we need a diferent recursion to deal with such formulas
extHMM hmm (Prob comp x path) i	=  (HMM {statesHMM = statesHMM hmm, 
                                         pTransHMM = pTransHMM hmm,
                                         labelFHMM = newLabel, 
                                         obsHMM = obsHMM hmm,						
                                         pObsHMM = pObsHMM hmm, 
                                         initDiHMM = initDiHMM hmm}, 
                                    j+1)
  where
    newLabel = listArray (bounds lab)
               [if (elem (edos!k) sat)
                then (lab!k)++["ap"++show j]
                else (lab!k) | k<-indices lab]		
    sat      = directApp newHMM (fst (renamePath path i)) comp x
    lab	     = labelFHMM newHMM					
    edos     = statesHMM newHMM			
    (newHMM, j)= extHMMPath hmm path i 

----------------------------------------------------
----------------------------------------------------
-- It returns the name of the new atomic proposition that replaces the original formula, that name depends on the int argument. 
-- It also returns the counter used when generating new atomic names
-- rename (OP (AtomP "w") (NoP (AtomP "r"))) 0
-- (ap1,2)
rename :: POCTL -> Int -> (POCTL, Int)
rename VerdadP i    = (VerdadP, i)
rename FalsoP  i    = (FalsoP, i)
rename (AtomP s) i  = (AtomP s, i)
rename (NoP p) i    = (AtomP ("ap"++show j), j+1)
	where 
		(_, j)	= rename p i
rename (OP p1 p2) i = (AtomP ("ap"++show k), k+1)
	where
		(_, j)  = rename p1 i				
                (_, k)	= rename p2 j
rename (YP p1 p2) i = (AtomP ("ap"++show k), k+1)
	where
		(_, j)  = rename p1 i				
                (_, k)	= rename p2 j

rename (Prob _ _ path) i = (AtomP ("ap"++show j), j+1)
	where
		(_, j)  = renamePath path i

----------------------------------------------------
----------------------------------------------------
-- It returns the extended HMM with the updated labelling function, it works for path formulas
-- We must remember that the algortithm renames only state formulas, no path formulas, that is why
-- we do not see many changes in these extended HMMs
extHMMPath :: HMM -> PathF -> Int -> (HMM, Int)
extHMMPath hmm (FormP phi) i 	= extHMM hmm phi i
extHMMPath hmm (NoPath path) i 	= extHMMPath hmm path i
extHMMPath hmm (OPath p1 p2) i 	= extHMMPath tmpHMM p2 j
	where
		(tmpHMM, j) = extHMMPath hmm p1 i 
extHMMPath hmm (YPath p1 p2) i 	= extHMMPath tmpHMM p2 j
	where
		(tmpHMM, j) = extHMMPath hmm p1 i
extHMMPath hmm (NextPath _ path) i = extHMMPath hmm path i
extHMMPath hmm (UntilBPath _ p1 p2) i = extHMMPath tmpHMM p2 j
	where
		(tmpHMM, j) = extHMMPath hmm p1 i
extHMMPath hmm (UntilPath p1 p2) i = extHMMPath tmpHMM p2 j
	where
		(tmpHMM, j) = extHMMPath hmm p1 i
                
----------------------------------------------------
----------------------------------------------------
-- Renames the path formulas to get their corresponding atomic propositional names
-- We must remember that the algortithm renames only state formulas, no path formulas, that is why
-- we do not see many changes in these POCTL* formulas
renamePath :: PathF -> Int -> (PathF, Int)
renamePath (FormP phi)	i	 = (FormP psi, j)
	where
		(psi, j) =  rename phi i 
renamePath (NoPath path) i 	 = (NoPath p, j) 
	where
		(p, j) = renamePath path i
renamePath (OPath p1 p2) i 	 = (OPath q1 q2, k) 
	where
		(q1, j) = renamePath p1 i				
                (q2, k) = renamePath p2 j
renamePath (YPath p1 p2) i 	 = (YPath q1 q2, k) 
	where
		(q1, j) = renamePath p1 i				
                (q2, k) = renamePath p2 j
renamePath (NextPath xs path) i = (NextPath xs p, j)
        where           
                (p, j) = renamePath path i
renamePath (UntilBPath n p1 p2) i = (UntilBPath n path1 path2, k)
         where
                (path1, j) = renamePath p1 i
                (path2, k) = renamePath p2 j
renamePath (UntilPath p1 p2) i = (UntilPath path1 path2, k)
         where
                (path1, j) = renamePath p1 i
                (path2, k) = renamePath p2 j
