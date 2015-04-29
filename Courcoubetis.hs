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

module Courcoubetis where

import Math.LinearEquationSolver
import Data.Array	
import Data.List
import Data.Ratio
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace

----------------------------------------------------
----------------------------------------------------
-- Data type for DTMCs
data DTMC a = DTMC {
  statesDTMC	:: Array Int a,		    -- States
  pTransDTMC	:: Array (Int, Int) Double, -- State Transition probabilities
  labelFDTMC	:: Array Int [String],	    -- Labelling Function
  initDiDTMC    :: Array Int Double	    -- Initial Distribution Matrix
  } deriving (Show)

----------------------------------------------------
----------------------------------------------------
-- Data type for the DTMC states that we obtain by transforming the HMM
data Courcou a = Base a | Par (Courcou a, String)

-- Instantiating the Show class for Courcou data type
instance (Show a) => Show (Courcou a) where
	show = showC

showC :: Show a => Courcou a -> String
showC (Base n)     = show n
showC (Par (c, s)) = "(" ++ showC c ++ "," ++ s ++ ")"

-- Instanciating the Eq class for Courcou data type
instance (Eq a) => Eq (Courcou a) where
	(==) = eqC

eqC :: Eq a => (Courcou a) -> (Courcou a) -> Bool
eqC (Base n) (Base m) 		= n==m
eqC (Base _) _ 			= False
eqC _ (Base _)			= False
eqC (Par (c1,s1)) (Par (c2,s2))	= (eqC c1 c2) && (s1 == s2)

-- This function allows us to get the first component of an
-- element of type Courcou a
first :: Courcou a -> Courcou a
first (Base _) 	  = error "There is no first for this pattern"
first (Par (f,_)) = f

-- This functions allows us to get the second component of an
-- element of type Courcou a
second :: Courcou a -> [Char]
second (Base _)	   = error "There is no second for this pattern"
second (Par (_,s)) = s

----------------------------------------------------
----------------------------------------------------
--Data type for the atomic propositions
data AtomElem = Simple String | ObSet [Int]

----------------------------------------------------
----------------------------------------------------
-- Data type for the LTL modal temporal logic
data LTL  = Verdad | Falso | Atom AtomElem | No LTL | O LTL LTL | Y LTL LTL
			| Next LTL | UntilB Int LTL LTL | Until LTL LTL

-- Instantiating the Show class for the LTL data type			
instance Show LTL where
	show = ltlStr

ltlStr :: LTL -> String
ltlStr Verdad			= "T"
ltlStr Falso			= "F"
ltlStr (Atom (Simple str)) 	= str
ltlStr (Atom (ObSet xs))        = show xs
ltlStr (No p) 			= "~(" ++ ltlStr p ++ ")"
ltlStr (O p1 p2) 		= (ltlStr p1) ++ " v " ++ (ltlStr p2)
ltlStr (Y p1 p2) 		= (ltlStr p1) ++ " ^ " ++ (ltlStr p2)
ltlStr (Next p) 		= "X( " ++ ltlStr p ++ " )"
ltlStr (UntilB n p1 p2) 	= (ltlStr p1) ++ " U[<=" ++ show n ++ "] " ++ (ltlStr p2)
ltlStr (Until p1 p2)    	= (ltlStr p1) ++ " U " ++ (ltlStr p2)

----------------------------------------------------
----------------------------------------------------
-- The Cx and Cu construction. 
-- Here we will get the new D' matrix
cxu :: Eq a => DTMC (Courcou (a, Int)) -- The original DTMC that is going to be extended 
                -> LTL                  -- The LTL formula from which the construction is based
                -> Int                  -- The number for the new variable
                -> (DTMC (Courcou (a, Int)), Int)
cxu m (Next phi) n 	= (DTMC {statesDTMC = newEdos, 
                                 pTransDTMC = newTransition p newM newEdos sY sN sQ solVect,
                                 labelFDTMC = newLabelling newM newEdos, 
                                 initDiDTMC = newInitDist newM newEdos sY sN solVect}	
                          , nextN)
  where 					
    (newM, nextN)= cxu m phi (n+1) 					
    (p, _)	 = reWrite phi (n+1) 					
    sY           = sYes p newM
    sN           = sNo p newM
    sQ           = sQM newM sY sN
    solVect	 = vectProb newM p sY sN 
    newEdos 	 = newStates newM n sY sN sQ 

cxu m (UntilB i phi1 phi2) n= (DTMC {statesDTMC = newEdos,					
                                     pTransDTMC = newTransitionU newM newEdos sYu sNu sQu solVect,
                                     labelFDTMC = newLabellingU newM newEdos,
                                     initDiDTMC = newInitDistU newM newEdos sYu sNu solVect}
			      , nextN)
  where 	                                	
    (tmpM, tmpN)  = cxu m phi1 (n+1)
    (newM, nextN) = cxu tmpM phi2 tmpN
    (p1, nn)	  = reWrite phi1 (n+1)					
    (p2, _)	  = reWrite phi2 nn
    solVect	  = vectProbU newM p1 p2 i
    sYu           = sYesU newM solVect
    sNu           = sNoU newM solVect
    sQu           = sQMU newM sYu sNu
    newEdos	  = newStatesU newM n sYu sNu sQu

cxu m (Until phi1 phi2) n= (DTMC {statesDTMC = newEdos,					
                                  pTransDTMC = newTransitionU newM newEdos sY sN sQ solVect,
                                  labelFDTMC = newLabellingU newM newEdos,
                                  initDiDTMC = newInitDistU newM newEdos sY sN solVect}
			   , nextN)
  where 	                                	
    (tmpM, tmpN)  = cxu m phi1 (n+1)
    (newM, nextN) = cxu tmpM phi2 tmpN
    (p1, nn)	  = reWrite phi1 (n+1)					
    (p2, _)	  = reWrite phi2 nn
    sN            = sNoUU p1 p2 newM
    sY            = sYesUU p1 p2 sN newM
    sQ            = sQMUU newM sY sN
    solVect	  = vectProbUU newM sY sQ
    newEdos	  = newStatesU newM n sY sN sQ

cxu m (No p)	n 	= cxu m p n
cxu m (O p1 p2) n 	= cxu newM p2 nextN
  where (newM, nextN)   = cxu m p1 n
cxu m (Y p1 p2) n 	= cxu newM p2 nextN
  where (newM, nextN)   = cxu m p1 n
cxu m _  n		= (m,n)	

-- And the new formula psi is got with the function reWrite that appears next
reWrite :: LTL -> Int -> (LTL, Int)
reWrite Verdad n	= (Verdad, n)
reWrite Falso n		= (Falso , n)
reWrite (Atom e) n	= (Atom e, n)
reWrite (No p) n	= (No  pp, nextN)
	where (pp, nextN) = reWrite p n
reWrite (O p1 p2) n	= (O pp1 pp2, nextN2)
	where
		(pp1, nextN1) = reWrite p1 n
		(pp2, nextN2) = reWrite p2 nextN1
reWrite (Y p1 p2) n	= (Y pp1 pp2, nextN2)
	where
		(pp1, nextN1) = reWrite p1 n
		(pp2, nextN2) = reWrite p2 nextN1
reWrite (Next p) n      = (Atom (Simple ("xi"++show n)), nextN)
	where (_, nextN) = reWrite p (n+1)
reWrite (UntilB _ p1 p2) n = (Atom (Simple ("xi"++show n)), nextN)
	where 
		(_, tmpValue)	= reWrite p1 (n+1)					
                (_, nextN) 	= reWrite p2 tmpValue
reWrite (Until p1 p2) n = (Atom (Simple ("xi"++show n)), nextN)
	where 
		(_, tmpValue)	= reWrite p1 (n+1)					
                (_, nextN) 	= reWrite p2 tmpValue

----------------------------------------------------
----------------------------------------------------
-- This function gets the observation that is the second component
-- of the state produced by transforming the HMM into a DTMC
getObs :: Eq a => Courcou (a, Int) -> Int
getObs (Base (_, o)) = o
getObs (Par (a, _))  = getObs a

----------------------------------------------------
----------------------------------------------------
-- The next function computes the set of states that satisfy the LTL formula
-- Notice that sat only handles the case when the LTL formula is propositional. 
-- The temporal operators are not considered since this function is invoked
-- on formulas that are temporal operator free. Specifically, we identify the 
-- more nested temporal operator and apply the sat function to its argument
sat :: Eq a => DTMC (Courcou (a, Int)) -> LTL -> [Courcou (a, Int)]
sat m Verdad		= elems (statesDTMC m)
sat _ Falso		= []
sat m (Atom (Simple s))	= [ edos!ind | ind<-indices labl, elem s (labl!ind)]
	where
		labl = labelFDTMC m			
                edos = statesDTMC m
sat m (Atom (ObSet xs))	= [ edos!ind | ind<-indices labl, elem (getObs (edos!ind)) xs]
	where
		labl = labelFDTMC m			
                edos = statesDTMC m
sat m (No p) 		= [ edos!ind | ind<-indices edos, not (elem (edos!ind) (sat m p))]
	where 
		edos = statesDTMC m
sat m (O p1 p2) 	= union (sat m p1) (sat m p2)
sat m (Y p1 p2) 	= intersect (sat m p1) (sat m p2)
sat m _			= error "The function sat does not know how to handle temporal operators"

----------------------------------------------------
----------------------------------------------------
-- The partioning of the set of states in computed next
-- SYes
-- By definition there must be at least one outgoing transition for each state 
-- that has positive probability
sYes :: Eq a => LTL -> DTMC (Courcou (a, Int)) -> [Courcou (a, Int)]
sYes phi mC = [edos!i | i<-indices edos, checkAll i]
  where
    edos = statesDTMC mC			
    checkAll ind = and [ if (pTransDTMC mC)!(ind, j) > 0 
                         then elem (edos!j) mysat
                         else True
                       | j<-indices edos] 
      where
        mysat = sat mC phi

-- SNo
sNo :: Eq a => LTL -> DTMC (Courcou (a, Int)) -> [Courcou (a, Int)]
sNo phi mC = [edos!i | i<-indices edos, checkAll i]
  where
    edos = statesDTMC mC			
    checkAll ind = and [ if (pTransDTMC mC)!(ind, j) > 0 
                         then not(elem (edos!j) mysat)
                         else True
                       | j<-indices edos] 
      where
        mysat = sat mC phi

-- S?
sQM :: Eq a => DTMC (Courcou (a, Int)) 
               -> [Courcou (a, Int)]
               -> [Courcou (a, Int)]
               -> [Courcou (a, Int)]
sQM mC xY xN = elems (statesDTMC mC) \\ (xY ++ xN)

----------------------------------------------------
----------------------------------------------------
-- We compute the new states with this function
newStates :: Eq a => DTMC (Courcou (a, Int))        -- The current DTMC 
                     -> Int                         -- The number for the new variable that will replace the most nested non-atomic LTL formula
                     -> [Courcou (a, Int)]          -- The set sYes
                     -> [Courcou (a, Int)]          -- The set sNo
                     -> [Courcou (a, Int)]          -- The set sQ
                     -> Array Int (Courcou (a, Int))-- The resulting array with the new states
newStates mC n yes no qMark = array (1, length asoccL) (zip [1..] asoccL)
  where
    edos   = elems (statesDTMC mC)				
    asoccL = [ if elem s yes 
               then Par (s,"xi"++show n) 
               else if elem s no 
                    then Par (s, "noXi"++show n) 
                    else Par (s, "xi"++show n) | s<-edos]
             ++ [Par (s, "noXi"++show n) | s<-edos, elem s qMark]			
                         
----------------------------------------------------
----------------------------------------------------
-- Function that computes the new initial distribution
newInitDist :: Eq a => DTMC (Courcou (a, Int))           -- The current DTMC
                       -> Array Int (Courcou (a, Int))   -- The new set of states
                       -> [Courcou (a, Int)]             -- The set sYes
                       -> [Courcou (a, Int)]             -- The set sNo
                       -> Array Int Double               -- The array with the probabilities that each state satisfies the temporal formula
                       -> Array Int Double               -- The resulting array with the new initial distribution
newInitDist mC newStat yes no vect = listArray (bounds newStat) 
                                      [computeInitDis (getInd mC (first edo)) edo | edo<- elems newStat]
  where
    computeInitDis indU (Par (u,atom)) | (elem u yes) || (elem u no) =  initDist!indU
                                       | (take 2 atom /= "no")       = (initDist!indU)*(vect!indU)
                                       | otherwise		     = (initDist!indU)*(1-(vect!indU))
    computeInitDis _ _ = error "This case shouldn't happen"	
    initDist = initDiDTMC mC	

----------------------------------------------------
----------------------------------------------------
-- Now we update the labelling function
newLabelling :: Eq a => DTMC (Courcou (a, Int))         -- The current DTMC 
                       -> Array Int (Courcou (a, Int)) -- The new set of states
                       -> Array Int [String]           -- The resulting array with the new labelling function for each state
newLabelling mC newStat = listArray (bounds newStat) [getAtom edo | edo<-elems newStat]
  where
    getAtom (Par (u, atom)) | (take 2 atom /= "no")	= (labelFDTMC mC)!(getInd mC u) ++ [atom]
    			    | otherwise			= (labelFDTMC mC)!(getInd mC u)

----------------------------------------------------
----------------------------------------------------
-- We compute the new state transition matrix
newTransition :: Eq a => LTL                             -- The temporal formula that is being replaced
			 -> DTMC (Courcou (a, Int))      -- The current DTMC                          
                  	 -> Array Int (Courcou (a, Int)) -- The new set of states 
                         -> [Courcou (a, Int)]           -- The set sYes
                         -> [Courcou (a, Int)]           -- The set sNo
                         -> [Courcou (a, Int)]           -- The set sQ
                         -> Array Int Double             -- The array with the probabilities that each state satisfies the temporal formula
                         -> Array (Int, Int) Double      -- The resulting array with the new transition probabilities
newTransition phi mC newStat yes no qMark vect = array ((1,1), (sb, sb)) lista
  where
    sb = snd (bounds newStat)				
    lista = [ ((i,j), getVal mC phi (newStat!i) (newStat!j) yes no qMark vect) | i<-[1..sb], j<-[1..sb]]

----------------------------------------------------
----------------------------------------------------
-- Auxiliary functions
-- This one computes the value for each matrix entry
getVal :: Eq a => DTMC (Courcou (a, Int))	-- The current DTMC 
                  -> LTL                        -- The temporal formula that is being replaced
                  -> Courcou (a, Int)           -- The source state from which the transition is defined 
                  -> Courcou (a, Int)           -- The destination state to which the transition is defined
                  -> [Courcou (a, Int)]         -- The set sYes
                  -> [Courcou (a, Int)]         -- The set sNo
                  -> [Courcou (a, Int)]         -- The set sQ
                  -> Array Int Double           -- The array with the probabilities that each state satisfies the temporal formula
                  -> Double                     -- The value for this transition
getVal mC phi (Par (u,x)) (Par (v,y)) yes no qMark vect
  | (elem u yes || elem u no)= if (elem v yes || elem v no) 
                               then pTran!(gu, gv)
                               else if (take 2 y /= "no") 
                                    then (pTran!(gu, gv))*(gQv)
                                    else (pTran!(gu, gv))*(1-gQv) 
  | elem v qMark  	     = if (take 2 x /= "no")
                              then if vSatPhi
                                   then if (take 2 y /= "no") 
                                        then (pTran!(gu, gv))*(gQv)/(gQu) 
                                        else (pTran!(gu, gv))*(1-gQv)/(gQu)
                                   else 0
                              else if (not vSatPhi)
                                   then if (take 2 y /= "no") 
                                        then (pTran!(gu, gv))*(gQv)/(1-gQu) 
                                        else (pTran!(gu, gv))*(1-gQv)/(1-gQu)
                                   else 0
  | (elem v yes || elem v no)= if vSatPhi
                               then if (take 2 x /= "no") 
                                    then (pTran!(gu, gv))/(gQu) 
                                    else 0
                               else if (take 2 x == "no") 
                                    then (pTran!(gu, gv))/(1-gQu) 
                                    else 0
  | otherwise		     = 0
  where 
    gu = getInd mC u                        
    gv = getInd mC v                             
    gQu = vect!gu                                   
    gQv = vect!gv                                         
    pTran = pTransDTMC mC                                                 
    vSatPhi = elem v (sat mC phi)

-- This method helps us to determine the state's index in a Markov chain
getInd :: Eq a => DTMC (Courcou (a, Int)) -> Courcou (a, Int) -> Int
getInd mC s = case elemIndex s sts of 
                Just x    -> x+1
                otherwise -> error "Error trying to get index of element"
	where sts = elems (statesDTMC mC)

-- Given a matrix this function returns the ith row
row :: (Ix a, Ix b) => a -> Array (a,b) c -> Array b c
row i m = ixmap (l',u') (\j->(i,j)) m
	where ((_,l'),(_,u')) = bounds m

-- This function computes the values (qu) needed by the construction cxu and stores them in an array
vectProb :: Eq a => DTMC(Courcou (a, Int))	  -- The current DTMC
                    -> LTL                        -- The LTL formula that is the operand of the next operator
                    -> [Courcou (a, Int)]         -- The set sYes
                    -> [Courcou (a, Int)]         -- The set sNo
                    -> Array Int Double
vectProb mC phi yes no = listArray (bounds st) [if elem (st!i) yes
                                                then 1
                                                else if elem (st!i) no
                                                     then 0
                                                     else auxSum mC mysat i
                                               | i<-indices st]
  where
    st    = statesDTMC mC
    mysat = sat mC phi

-- Auxiliary function that calculates the sum of the probabilities of
-- the states satisfying the formula phi reachable from state i
auxSum :: Eq a => DTMC(Courcou (a, Int)) -> [Courcou (a, Int)] -> Int -> Double
auxSum mC mysat ind = sum [ myRow!j | j<-(map (getInd mC) mysat)]
  where 
    myRow = row ind (pTransDTMC mC)
    
--------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------
-- The Cu construction appears next. (The bounded version).
--------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------

-- The partioning of the set of states for the construction of Cu is computed next
-- SYes
sYesU :: Eq a => DTMC (Courcou (a, Int)) -> Array Int Double -> [Courcou (a, Int)]
sYesU mC vect = [(st!i) | i<-indices st, (vect!i)==1] 
  where 
    st = statesDTMC mC

-- SNo
sNoU :: Eq a => DTMC (Courcou (a, Int)) -> Array Int Double -> [Courcou (a, Int)]
sNoU mC vect = [(st!i) | i<-indices st, (vect!i)==0] 
  where 
    st = statesDTMC mC

-- S?										
sQMU :: Eq a => DTMC (Courcou (a, Int)) 
                -> [Courcou (a, Int)]
                -> [Courcou (a, Int)]
                -> [Courcou (a, Int)]
sQMU mC yes no = elems (statesDTMC mC) \\ (yes ++ no)

----------------------------------------------------
----------------------------------------------------
-- We compute the new states with this function
newStatesU :: Eq a => DTMC (Courcou (a, Int))        -- The current DTMC 
                      -> Int                         -- The number for the new variable that will replace the most nested non-atomic LTL formula
                      -> [Courcou (a, Int)]          -- The set sYes
                      -> [Courcou (a, Int)]          -- The set sNo
                      -> [Courcou (a, Int)]          -- The set sQ
                      -> Array Int (Courcou (a, Int))-- The resulting array with the new states
newStatesU mC n yes no qMark = array (1, length asoccL) (zip [1..] asoccL)
  where
    edos   = elems (statesDTMC mC)
    asoccL = [ if elem s yes                         
               then Par (s,"xi"++show n) 
               else if elem s no                     
                    then Par (s, "noXi"++show n)                     
                    else Par (s, "xi"++show n) | s<-edos]             
             ++ [Par (s, "noXi"++show n) | s<-edos,                  
                 elem s qMark]							

----------------------------------------------------
----------------------------------------------------
-- Function that computes the new initial distribution
newInitDistU :: Eq a => DTMC (Courcou (a, Int))          -- The current DTMC
                        -> Array Int (Courcou (a, Int))  -- The new set of states
                        -> [Courcou (a, Int)]            -- The set sYes
                        -> [Courcou (a, Int)]            -- The set sNo
                        -> Array Int Double              -- The array with the probabilities that each state satisfies the temporal formula
                        -> Array Int Double              -- The resulting array with the new initial distribution
newInitDistU mC newStat yes no vect = listArray (bounds newStat) 
                                       [computeInitDis (getInd mC (first edo)) edo | edo<- elems newStat]
  where                                  
    computeInitDis indU (Par (u,atom)) | (elem u yes) || (elem u no) =  initDist!indU
                                       | (take 2 atom /= "no")       = (initDist!indU)*(vect!indU)
                                       | otherwise		     = (initDist!indU)*(1-(vect!indU))
    computeInitDis _ _ = error "This case shouldn't happen"
    initDist = initDiDTMC mC 
----------------------------------------------------
----------------------------------------------------
-- Now we update the labelling function
newLabellingU :: Eq a => DTMC (Courcou (a, Int))         -- The current DTMC 
                        -> Array Int (Courcou (a, Int)) -- The new set of states 
                        -> Array Int [String]           -- The resulting array with the new labelling function for each state
newLabellingU mC newStat = listArray (bounds newStat) [getAtom edo | edo<-elems newStat]
  where								
    getAtom s = (labelFDTMC mC)!(getInd mC (first s)) ++ [second s]


----------------------------------------------------
----------------------------------------------------
-- We compute the new state transition matrix for Cu
newTransitionU :: Eq a => DTMC(Courcou (a, Int))               -- The current DTMC
                          -> Array Int (Courcou (a, Int))      -- The new set of states
                          -> [Courcou (a, Int)]                -- The set sYes
                          -> [Courcou (a, Int)]                -- The set sNo
                          -> [Courcou (a, Int)]                -- The set sQ
                          -> Array Int Double                  -- The array with the probabilities that each state satisfies the temporal formula
                          -> Array (Int, Int) Double           -- The resulting array with the new transition probabilities
newTransitionU mC newStat yes no qMark vect = array ((1,1), (sb, sb)) lista
  where	
    sb     = snd (bounds newStat)		
    lista  = [ ((i,j), getValU mC (newStat!i) (newStat!j) yes no qMark vect)
             | i<-[1..sb], j<-[1..sb]]

----------------------------------------------------
----------------------------------------------------
-- Auxiliary functions
-- This one computes the value for each transition probability matrix entry
getValU :: Eq a => DTMC (Courcou (a, Int))	-- The current DTMC
                   -> Courcou (a, Int)          -- The start state from which the transition is defined 
                   -> Courcou (a, Int)          -- The destination state to which the transition is defined 
                   -> [Courcou (a, Int)]        -- The set sYes
                   -> [Courcou (a, Int)]        -- The set sNo
                   -> [Courcou (a, Int)]        -- The set sQ
                   -> Array Int Double          -- The array with the probabilities that each state satisfies the temporal formula
                   -> Double
getValU mC (Par (u,x)) (Par (v,y)) yes no qMark vect 
  | (elem u yes || elem u no)	= if (elem v yes || elem v no) 
                                  then pTran!(gu, gv)							
                                  else if (take 2 y /= "no")						
                                       then (pTran!(gu, gv))*(gQv)					
                                       else (pTran!(gu, gv))*(1-gQv)		  			
  | elem v qMark		= if (take 2 x /= "no")						
                                  then if (take 2 y /= "no")						
                                       then (pTran!(gu, gv))*(gQv)/(gQu)				
                                       else 0				
                                  else if (take 2 y == "no")						
                                       then (pTran!(gu, gv))*(1-gQv)/(1-gQu)				
                                       else 0				 	
  | elem v yes			= if (take 2 x /= "no")							
                                  then (pTran!(gu, gv))/(gQu)						
                                  else 0					  			
  | elem v no			= if (take 2 x == "no")							
                                  then (pTran!(gu, gv))/(1-gQu)						
                                  else 0				
  | otherwise			= 0	
  where 
    gu = getInd mC u
    gv = getInd mC v
    gQu = vect!gu
    gQv = vect!gv
    pTran = pTransDTMC mC

-- This function computes the values (qu) needed by the construction cu and stores them in an array
vectProbU :: Eq a => DTMC(Courcou (a, Int))	-- The current DTMC
                     -> LTL                     -- The LHS formula operand of the until operator
                     -> LTL                     -- The RHS formula operand of the until operator
                     -> Int                     -- The integer that bounds the until operator
                     -> Array Int Double        -- The array with the probabilities that each state satisfies the temporal formula
vectProbU mC phi1 phi2 m = listArray (1, length myList) myList                    
  where                           
    myList = auxVeProbU mC m yes qmark
    elemen = elems (statesDTMC mC)
    yes    = sat mC phi2
    no     = elemen \\ (union (sat mC phi1) yes) 
    qmark  = elemen \\ (yes ++ no)

-- Auxiliary function that computes the probability that (phi1 U phi2) is satisfied
-- in each state
auxVeProbU :: Eq a => DTMC(Courcou (a, Int))            -- The current DTMC
                      -> Int                            -- The integer that bounds the until operator
                      -> [Courcou (a, Int)]             -- The set sYes
                      -> [Courcou (a, Int)]             -- The set sQ
                      -> [Double]                       -- The list with the probabilities that each state satisfies the until formula
auxVeProbU mC 0 sY _  = [if elem edo sY then 1.0 else 0.0 | edo<-elems (statesDTMC mC)]
auxVeProbU mC m sY sQ = mult pPrime (auxVeProbU mC (m-1) sY sQ)			
  where 
    mult xss ys = [sum (zipWith (*) xs ys) | xs<-xss] 
    pPrime      = [if (elem s sQ) 
                        then elems (row (getInd mC s) (pTransDTMC mC))
                        else if (elem s sY)
                             then [if e==s then 1.0 else 0.0 | e<-statesM]
                             else replicate (length statesM) 0.0 
                  | s<-statesM]
    statesM     = elems (statesDTMC mC) 

--------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------
-- The Cu construction appears next. (The unbounded version)
--------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------
-- The partioning of the set of states for the construction of Cu is computed next
-- Set No
-- The set for which the p_s(p U q) is exactly 0
sNoUU :: Eq a => LTL -> LTL -> DTMC (Courcou (a, Int)) -> [Courcou (a, Int)]
sNoUU phi1 phi2 mC = (elems (statesDTMC mC)) \\ (probNo mC (map (getInd mC) satPhi1) satPhi2 (map (getInd mC) satPhi2)) 
  where
    satPhi1 = sat mC phi1
    satPhi2 = sat mC phi2

-- An auxiliary function to compute the fixed point needed to obtain the set No 
probNo :: Eq a => DTMC (Courcou (a, Int)) 
                  -> [Int] 
                  -> [Courcou (a, Int)] 
                  -> [Int]
                  -> [Courcou (a, Int)] 
probNo mC sat1Ind sat2 myInd = if sat2 == nL
                               then sat2 
                               else probNo mC (sat1Ind \\ newIndices) nL newIndices
  where
    nL = union sat2 [st!i | i<-sat1Ind,
                     findState (row i (pTransDTMC mC)) myInd]
    findState _ [] = False
    findState arr (n:ns) = if arr!n > 0
                           then True 
                           else findState arr ns
    st = statesDTMC mC
    newIndices = (map (getInd mC) (nL \\ sat2))
    
-- Set Yes
-- The set for which the p_s(p U q) is exactly 1
sYesUU :: Eq a => LTL -> LTL -> [Courcou (a, Int)] -> DTMC (Courcou (a, Int)) -> [Courcou (a, Int)]
sYesUU phi1 phi2 sN mC = (elems (statesDTMC mC)) \\ (probYes mC (map (getInd mC) diffSet) sN (map (getInd mC) sN))
  where
    diffSet = (sat mC phi1) \\ (sat mC phi2)

-- An auxiliary function to compute the fixed point needed to obtain the set Yes 
probYes :: Eq a =>  DTMC (Courcou (a, Int)) 
                    -> [Int] 
                    -> [Courcou (a, Int)] 
                    -> [Int]
                    -> [Courcou (a, Int)] 
probYes mC diffInd sN myInd = if sN == nL                       
                              then sN                         
                              else probYes mC (diffInd \\ newIndices) nL newIndices
  where
    nL = union sN [st!i | i<-diffInd,
                   findState (row i (pTransDTMC mC)) myInd]
    findState _ [] = False
    findState arr (n:ns) = if arr!n > 0
                           then True 
                           else findState arr ns
    st = statesDTMC mC
    newIndices = (map (getInd mC) (nL \\ sN))

-- Set ?
-- The states that are neither in sYesUU nor in sNoUU
sQMUU :: Eq a => DTMC (Courcou (a, Int)) 
         -> [Courcou (a, Int)] 
         -> [Courcou (a, Int)] 
         -> [Courcou (a, Int)] 
sQMUU mC sY sN = (elems (statesDTMC mC)) \\ (sY ++ sN)

-- In order to find the probability that a state in set ? satisfies the 
-- formula (p U q) we need to solve a linear equation system (LES) of the  
-- form Mx=b, where M=I-A(a modified version of the transition probability matrix) 
-- and b is a column with 1 in the i-row if the i state is in the set Yes, and 0 otherwise.
-- The next function computes the matrix M involved in the LES.
aMat :: Eq a => DTMC (Courcou (a, Int)) 
                  -> [Courcou (a, Int)] 
                  -> [[Rational]]
aMat mC sQ = [if elem (st!i) sQ 
                then (rowPrime i trans)
                else [if j==i 
                      then 1.0 
                      else 0.0| j<-ind] 
                | i<-ind]
  where
    st    = statesDTMC mC
    trans = pTransDTMC mC
    ind   = indices st
    
-- This is an auxiliary function that returns the i column of the
-- previous M matrix. Notice how in the diagonal we substract 
-- from 1 the probability P(s,s), elsewhere we have the probability 
-- negated, i.e. -P(s,s')
rowPrime :: (Ix a, Real b) => a -> Array (a,a) b -> [Rational]
rowPrime i m = [if k==i 
                then toRational (1 - (m!(i,k)))             
                else toRational (  - (m!(i,k))) | k<-range (l',u')] 
  where ((_,l'),(_,u')) = bounds m
        
-- b is a column with 1 in the position corresponding to a state in the set Yes, and 0 otherwise.
bCol :: Eq a => DTMC (Courcou (a, Int)) 
                  -> [Courcou (a, Int)]           
                  -> [Rational]
bCol mC yes = [if elem st yes 
               then 1 
               else 0 | st<-elems (statesDTMC mC)]
             
--  This function computes the probabilities that each state satisfies the until formula           
vectProbUU :: Eq a =>  DTMC (Courcou (a, Int))    -- The current DTMC
                       -> [Courcou (a, Int)]      -- The set Yes
                       -> [Courcou (a, Int)]      -- The set ?
                       -> Array Int Double        -- The array with the probabilities that each state satisfies the until formula
vectProbUU mC sY sQ = listArray (1, length myL) myL 
  where
    myL = case unsafePerformIO (solveRationalLinearEqs Z3 (aMat mC sQ) (bCol mC sY)) of 
                        Just xs   -> map (\r->fromRational r) xs 
                        otherwise -> error "There are no solutions of the linear equation system"
