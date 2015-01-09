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

module DirectApproach where

import Courcoubetis
import Data.Array
import Data.List
import Debug.Trace

----------------------------------------------------
----------------------------------------------------
-- Data type for HMMs
data HMM = HMM {
  statesHMM	:: Array Int Int,	        -- States
  pTransHMM	:: Array (Int, Int) Double,     -- State Transition Matrix
  labelFHMM	:: Array Int [String],  	-- Labelling Function
  obsHMM	:: [Int],		   	-- Set of observation
  pObsHMM	:: Array (Int, Int) Double,	-- Observaton Probability Matrix
  initDiHMM	:: Array Int Double		-- Initial Distribution Matrix
  } deriving (Show)

{-estadosHMM :: Array Int Int
estadosHMM = array (1,2) [(1,1) , (2,2)]

matrixHMM :: Array (Int, Int) Double
matrixHMM = array ((1,1), (2,2)) 
				[((1,1), 0.7), ((1,2), 0.3),
				 ((2,1), 0.4), ((2,2), 0.6)]

etiqHMM :: Array Int [String]
etiqHMM = array (1,2) [(1,["p"]), (2,["q"])]

myObsHMM :: [Int]
myObsHMM = [1,2,3]

obsMatHMM :: Array (Int,Int) Double
obsMatHMM = array ((1,1),(2,3))
            [((1,1), 0.1), ((1,2), 0.4), ((1,3), 0.5),
             ((2,1), 0.7), ((2,2), 0.2), ((2,3), 0.1)]

initHMM :: Array Int Double
initHMM = array (1,2) [(1, 0.6), (2, 0.4)]

myHMM = HMM {statesHMM = estadosHMM, pTransHMM = matrixHMM, labelFHMM = etiqHMM, 
				obsHMM = myObsHMM, pObsHMM = obsMatHMM, initDiHMM = initHMM}
-}

----------------------------------------------------
----------------------------------------------------
-- Data type for POCTL*
-- State Formulas
-- To remove the grammar's ambiguity I do not have a data type for Belief States Formulas, instead I
-- add its expressive power to the POCTL* data type that appears next
data POCTL  = VerdadP | FalsoP | AtomP String | NoP POCTL | OP POCTL POCTL | YP POCTL POCTL | Prob String Double PathF

instance Show POCTL where
	show = poctlS

poctlS :: POCTL -> String
poctlS VerdadP		= "Verdad"
poctlS FalsoP 		= "Falso"
poctlS (AtomP s)	=  s
poctlS (NoP p)		= "~" ++ poctlS p
poctlS (OP p1 p2)	= "(" ++ (poctlS p1) ++ " v " ++ (poctlS p2) ++ ")"
poctlS (YP p1 p2)       = "(" ++ (poctlS p1) ++ " ^ " ++ (poctlS p2) ++ ")"
poctlS (Prob c f path)	= "Pr [" ++ c ++ show f ++ "] (" ++ show path ++ ")"

-- Path Formulas
data PathF  = FormP POCTL | NoPath PathF | OPath PathF PathF | YPath PathF PathF
		| NextPath [Int] PathF | UntilBPath Int PathF PathF | UntilPath PathF PathF

instance Show PathF where
	show = pathS

pathS :: PathF -> String

pathS (FormP phi)	  = poctlS phi
pathS (NoPath p)	  = "~(" ++ pathS p ++ ")"
pathS (OPath p1 p2)	  = "(" ++ (pathS p1) ++ " v " ++ (pathS p2) ++ ")"
pathS (YPath p1 p2)	  = "(" ++ (pathS p1) ++ " ^ " ++ (pathS p2) ++ ")"
pathS (NextPath obs p)	  = "X_" ++ show obs ++ " (" ++ pathS p ++ ")"
pathS (UntilBPath n p1 p2)= "(" ++ (pathS p1) ++ " U<=" ++ show n ++ " " ++ (pathS p2) ++ ")"
pathS (UntilPath p1 p2)   = "(" ++ (pathS p1) ++ " U " ++ (pathS p2) ++ ")"

--formula :: POCTL
--formula = YP (NoP (AtomP "b")) (Prob "<" 0.05 (UntilPath (FormP (AtomP "a")) (NextPath [1] (FormP (AtomP "b")))) )
--formula = YP (NoP (AtomP "b")) (Prob "<" 0.05 (UntilBPath 10000 (FormP (AtomP "a")) (FormP (AtomP "b"))))
--formula = Prob ">" 0.98 (UntilBPath 2 (FormP VerdadP) (FormP (AtomP "succ")))

----------------------------------------------------
----------------------------------------------------
-- This function transforms an HMM into a DTMC.
-- Here we perform the transformation from an HMM to a DTMC, so the new 
-- state set is S'=S x O, P'((s,o),(s',o')) = P(s,s')b(s',o'), Mu(s',o')=Mu(s)b(s',o') and L'(s,o)=L(s)u{Omega c O|o in Omega} 
-- Notice two things: First, the labelling function works as previously has done it, the observation part
-- is going to be added later on. Second, the initial distribution function has been modified according 
-- to the new states
satQOSHMM :: HMM -> DTMC (Courcou (Int,Int))
satQOSHMM hmm = DTMC {statesDTMC = getStates, 			
                      pTransDTMC = newTrans, 			
                      labelFDTMC = newLabel, 					
                      initDiDTMC = initialT}		
  where	
    tmpList	= [Base (s,o) | s<-elems (statesHMM hmm), o<-(obsHMM hmm)]	
    tmpLength	= length tmpList	
    obsLen	= length (obsHMM hmm)
    getStates	= listArray (1, tmpLength) tmpList	
    newTrans	= array ((1,1), (tmpLength, tmpLength))
                  [((n,m), (pTransHMM hmm)!((div (n-1) obsLen)+1, (div (m-1) obsLen)+1) * 
                           (pObsHMM hmm)!((div (m-1) obsLen)+1, (mod (m-1) obsLen)+1))
                  | n<-[1..tmpLength], m<-[1..tmpLength]]
    newLabel 	= array (1, tmpLength) [(i, (labelFHMM hmm)!((div (i-1) obsLen)+1))
                                       | i<-[1..tmpLength]]	
    initialT 	= array (1, tmpLength) [(i, (initDiHMM hmm)!((div (i-1) obsLen)+1) * 
                                            (pObsHMM hmm)!((div (i-1) obsLen)+1, (mod (i-1) obsLen)+1)) 
                                       | i<-[1..tmpLength]]

----------------------------------------------------
----------------------------------------------------
-- Function that transforms QOS formula into QLS fromulas
transForm :: PathF -> LTL
transForm (FormP (AtomP s))	= Atom (Simple s)
transForm (FormP VerdadP)	= Verdad
transForm (FormP FalsoP)	= Falso
transForm (NoPath p) 		= No (transForm p)
transForm (OPath p q)		= O (transForm p) (transForm q)
transForm (YPath p q)           = Y (transForm p) (transForm q)
transForm (NextPath xs p)	= Y (Atom (ObSet xs)) (Next (transForm p))
transForm (UntilBPath n p q)    = UntilB n (transForm p) (transForm q)
transForm (UntilPath p q)       = Until (transForm p) (transForm q)
transForm _			= error "This case shouldn't happen. Because the formula we are considering is a maximal state subformula"

----------------------------------------------------
----------------------------------------------------
-- This function returns the very first component of the state
-- produced by transforming the HMM to a DTMC
origin :: Courcou (a, Int) -> a
origin (Base (n, _)) 	= n
origin (Par (cou, _))	= origin cou

----------------------------------------------------
----------------------------------------------------
-- Function that determines if the satisfying probabilities
-- are within the reqired range
comparison :: HMM -> String -> Double -> [Double] -> [Int]
comparison hmm strComp x ys = compAux hmmStat boolList 
  where
    hmmStat	= elems (statesHMM hmm)
    boolList    = map comp ys
    comp doub 	= compOp doub x
    compOp      = case strComp of
			"<=" -> (<=)
			"<"  -> (<)
			">=" -> (>=)
			otherwise -> (>)

-- Auxiliary function that matches the state and its boolean value
compAux :: [Int] -> [Bool] -> [Int]
compAux [] [] = []
compAux _ [] = error "Cannot carry out comparison."
compAux [] _ = error "Cannot carry out comparison."
compAux (x:xs) (False:bs)= compAux xs bs
compAux (x:xs) (True:bs) = x:(compAux xs bs) 

----------------------------------------------------
----------------------------------------------------
-- Given a list of pairs having the form (State, Probability), 
-- returning a list with the respective summation for each HMM state
findSummation :: [(Int, Double)] -> Int -> [Double]
findSummation xs size = findSummationAux xs ys 
  where
    ys = replicate size 0.0
    
-- Auxiliary function that computes the summation for each state
-- updating a temporary list ys
findSummationAux :: [(Int, Double)] -> [Double] -> [Double]
findSummationAux [] ys = ys
findSummationAux (x:xs) ys = findSummationAux xs (updateList (fst x) ys (snd x))

-- This function updates the position n of the temporary list (y:ys)
updateList :: Int -> [Double] -> Double -> [Double]
updateList _ [] _ = error "Incorrect index value."
updateList 1 (y:ys) val = (y+val):ys
updateList n (y:ys) val = y:(updateList (n-1) ys val)

----------------------------------------------------
----------------------------------------------------
-- This method computes the satisfying probability of all HMM states 
-- given the DTMC m and the set of DTMC states that satisfy the specification,
-- this corresponds to a summation of initial distributions of m
probVal :: DTMC (Courcou (Int, Int)) -> Int -> [Courcou (Int, Int)] -> [Double]
probVal m size sat = trace ("(Probability of satisfaction of each state: " ++ show summation ++ ")") summation
  where
    summation   = findSummation val size
    val 	= [(origin(dtmcStat!j), (initDiDTMC m)!j) | j<-indices dtmcStat, elem (dtmcStat!j) sat]
    dtmcStat	= statesDTMC m

----------------------------------------------------
----------------------------------------------------
-- This function computes the HMM states whose satisfying probability for the LTL formula
-- is within the range establish by 'c' and 'x', the comparison operator and the real number
-- between 0 and 1, for this end we use the DTMC resulting of the HMM transformation
satisfy :: HMM-> DTMC (Courcou (Int, Int)) -> LTL -> String -> Double -> [Int]
satisfy hmm _ Verdad comp x = case comp of 
                              ">"  | x<1  -> elems (statesHMM hmm)
                              ">="        -> elems (statesHMM hmm)		
                              "<=" | x==1 -> elems (statesHMM hmm)	
                              otherwise -> []
satisfy hmm _ Falso  comp x = case comp of 
  			      "<"  | x>0  -> elems (statesHMM hmm) 
                              "<="        -> elems (statesHMM hmm)	
                              ">=" | x==0 -> elems (statesHMM hmm)				
                              otherwise -> []
satisfy hmm m (Atom (Simple s)) comp x = comparison hmm comp x (probVal m size (sat m (Atom (Simple s))))
  where	
    hmmStat = statesHMM hmm
    size    = rangeSize (bounds hmmStat)
satisfy hmm m (No p) comp x = comparison hmm comp x (probVal myMC size (sat myMC ap))
  where							
    hmmStat 	= statesHMM hmm					
    size        = rangeSize (bounds hmmStat)
    (myMC, _) 	= cxu m (No p) 0								
    (ap, _)	= reWrite (No p) 0
satisfy hmm m (O p1 p2) comp x = comparison hmm comp x (probVal myMC size mySet)
  where							
    hmmStat 	   = statesHMM hmm
    size	   = rangeSize (bounds hmmStat)
    mySet 	   = union (sat myMC reWp1) (sat myMC reWp2)				
    (myMC, _)	   = cxu m (O p1 p2) 0							
    (O reWp1 reWp2, _) = reWrite (O p1 p2) 0
satisfy hmm m (Y p1 p2) comp x = comparison hmm comp x (probVal myMC size mySet)
  where							
    hmmStat            = statesHMM hmm	
    size 	       = rangeSize (bounds hmmStat)
    mySet 	       = intersect (sat myMC reWp1) (sat myMC reWp2)		
    (myMC, _)	       = cxu m (Y p1 p2) 0					
    (Y reWp1 reWp2, _) = reWrite (Y p1 p2) 0
satisfy hmm m (Next p) comp x = comparison hmm comp x (probVal myMC size (sat myMC ap)) 
  where						
    hmmStat 	= statesHMM hmm
    size	= rangeSize (bounds hmmStat)
    (myMC, _)	= cxu m (Next p) 0		
    (ap, _)	= reWrite (Next p) 0
satisfy hmm m (UntilB n p1 p2) comp x = comparison hmm comp x (probVal myMC size (sat myMC ap))
  where							
    hmmStat 	= statesHMM hmm
    size	= rangeSize (bounds hmmStat)
    (myMC, _)	= cxu m (UntilB n p1 p2) 0		
    (ap, _)	= reWrite (UntilB n p1 p2) 0
satisfy hmm m (Until p1 p2) comp x = comparison hmm comp x (probVal myMC size (sat myMC ap))
  where						
    hmmStat 	= statesHMM hmm
    size	= rangeSize (bounds hmmStat)
    (myMC, _)	= cxu m (Until p1 p2) 0	
    (ap, _)	= reWrite (Until p1 p2) 0
                                                                                                  
----------------------------------------------------
----------------------------------------------------
-- It returns the set of HMM's states satisfying the POCTL* path formula obtained from 
-- the probabilistic operator
directApp :: HMM -> PathF -> String -> Double -> [Int]
directApp hmm p comp x = satisfy hmm (satQOSHMM hmm) (transForm p) comp x
