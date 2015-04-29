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

module Parser where

import Data.Array
import Data.List
import Lexer
import ModelChecker
import DirectApproach
  
-- Function that takes a list of tokens and return the corresponding HMM  
parse :: [Token] -> Bool -> HMM 
parse t b = createHMM t b dummyHMM
  where dummyHMM = HMM {statesHMM = array (0,0) [(0,-1)],
                        pTransHMM = array ((0,0),(0,0)) [((0,0),-1)],
                        labelFHMM = array (0,0) [(0,[""])],
                        obsHMM = [],
                        pObsHMM = array ((0,0),(0,0)) [((0,0),-1)],
                        initDiHMM = array (0,0) [(0,-1.0)]}
                
-- This auxiliary function takes three by three tokens with which a                    
-- new element of the HMM is made up
createHMM :: [Token] -> Bool -> HMM -> HMM
createHMM [] _ hmm = hmm
createHMM ((Rsv St): ODef : (SetL n): moreTokens) bool hmm 
  | n <= 0 = error "The number of states must be a positive integer."
  | otherwise = createHMM moreTokens bool newHMM
  where
    newHMM = HMM {statesHMM = listArray (1,n) [1..n],
                    pTransHMM = pTransHMM hmm,                
                    labelFHMM = labelFHMM hmm,                
                    obsHMM = obsHMM hmm,                
                    pObsHMM = pObsHMM hmm,                
                    initDiHMM = initDiHMM hmm}
createHMM ((Rsv Trans): ODef : (ListDouble lstDouble): moreTokens) bool  hmm 
  | length lstDouble /= n*n = error "Error parsing the transition probability matrix. The size of the matrix is not correct."             
  | not (sumOne lstDouble n) = error "Error parsing the transition probability matrix. Some rows does not sum up to 1."     
  | otherwise = createHMM moreTokens bool newHMM 
  where
    st = statesHMM hmm
    newHMM = HMM {statesHMM = st,
                    pTransHMM = listArray ((1,1),(n,n)) lstDouble,                
                    labelFHMM = labelFHMM hmm,                
                    obsHMM = obsHMM hmm,                
                    pObsHMM = pObsHMM hmm,                
                    initDiHMM = initDiHMM hmm}
    n = rangeSize (bounds st)
createHMM ((Rsv Lbl): ODef : (ListAtom lstAtom): moreTokens) bool hmm 
  | length lstAtom /= n = error "Error parsing the labels. The number of lists of strings does not corresponds to the number of states."
  | otherwise = createHMM moreTokens bool newHMM 
  where
    st = statesHMM hmm
    newHMM = HMM {statesHMM = st,
                    pTransHMM = pTransHMM hmm,                
                    labelFHMM = listArray (1,n) lstAtom,                
                    obsHMM = obsHMM hmm,                
                    pObsHMM = pObsHMM hmm,                
                    initDiHMM = initDiHMM hmm}
    n = rangeSize (bounds st)
createHMM ((Rsv Obs): ODef : (SetL obs): moreTokens) bool hmm = createHMM moreTokens bool newHMM 
  where        
    newHMM = HMM {statesHMM = statesHMM hmm,
                  pTransHMM = pTransHMM hmm,                
                  labelFHMM = labelFHMM hmm,                
                  obsHMM = [1..obs],                
                  pObsHMM = pObsHMM hmm,                
                  initDiHMM = initDiHMM hmm}
createHMM ((Rsv ObsProb): ODef : (ListDouble lstDouble):moreTokens) bool hmm 
  | length lstDouble /= n*m =  error "Error parsing the observation probability matrix. Inadequate matrix size."
  | not (sumOne lstDouble m) =  error "Error parsing the observation probability matrix. No all of the rows of the matrix sum up to 1."
  | otherwise = createHMM moreTokens bool newHMM
  where
    st = statesHMM hmm
    obs = obsHMM hmm
    newHMM = HMM {statesHMM = st,
                  pTransHMM = pTransHMM hmm,                
                  labelFHMM = labelFHMM hmm,                
                  obsHMM = obs,                
                  pObsHMM = listArray ((1,1),(n,m)) lstDouble,                
                  initDiHMM = initDiHMM hmm}
    n = rangeSize (bounds st)
    m = length obs
createHMM ((Rsv IniDist): ODef : (Lista lstInitial): moreTokens) bool hmm 
  | length lstInitial /= n && (not bool) = error "Error parsing the initial distribution. The initial distributions list size is wrong." 
  | not (sumOne lstInitial n) && (not bool) = error "Error parsing the initial distribution. The initial distribution does not sum up to 1."
  | otherwise = createHMM moreTokens bool newHMM  
  where
    st = statesHMM hmm
    newHMM = HMM {statesHMM = st,
                    pTransHMM = pTransHMM hmm,                
                    labelFHMM = labelFHMM hmm,                
                    obsHMM = obsHMM hmm,                
                    pObsHMM = pObsHMM hmm,                
                    initDiHMM = if bool 
                                then listArray (1,n) (replicate n 1.0)  
                                else listArray (1,n) lstInitial}
    n = rangeSize (bounds st)
createHMM _ _ hmm = error "Error parsing unkown token."

-- This function takes a list a double numbers and checks whether the sum of their values is equal to 1
sumOne :: [Double] -> Int  -> Bool
sumOne [] _ = True
sumOne lst size = (sumVal <= 1.0  && sumVal >= 0.99999999999999) && (sumOne rest size)
  where
    sumVal = sum elemLst
    (elemLst, rest) = splitAt size lst
    
-- Given a list of TknPOCTLs returns the well formed POCTL* function.
-- Notice the use of the auxiliaty function parsePhi. The grammar used  
-- in this parser models the precedence of operators and is shown below:
--      Phi ::= Psi | Psi v Phi
--      Psi ::= Theta | Theta ^ Psi
--      Theta ::= True | False | a | ~Theta | (Phi) | P [comp x] A
-- where A is a path formula obtained by the grammar
--      A ::= B | B v A
--      B ::= C | C ^ B
--      C ::= D | D U C
--      D ::= E | E U n D
--      E ::= ~E | (A) | X_{obs} E | Theta
parsePOCTL :: [TknPOCTL] -> [Int] -> POCTL
parsePOCTL xs bs =
  case (parsePhi xs bs) of
    (formula, []) -> formula
    _             -> error "Parsing failed!"
    
-- This function parses the grammatical cathegory Phi ::= Psi | Psi v Phi
parsePhi :: [TknPOCTL] -> [Int] -> (POCTL, [TknPOCTL])
parsePhi tkns bs = 
  case rec of
    (LogOp Disj):left   -> let (phi, rmndr) = parsePhi left bs
                           in (OP psi phi, rmndr)
    _                   -> (psi, rec) 
  where
    (psi, rec) = parsePsi tkns bs
    
-- This function parses the grammatical cathegory Psi ::= Theta | Theta ^ Psi
parsePsi :: [TknPOCTL] -> [Int] -> (POCTL, [TknPOCTL])
parsePsi tkns bs =
  case rec of
    (LogOp Conj):left   -> let (psi, rmndr) = parsePsi left bs                   
                           in (YP theta psi, rmndr)
    _                   -> (theta, rec) 
  where
    (theta, rec) = parseTheta tkns bs
    
-- This function parses the grammatical cathegory Theta ::= True | False | a | ~Theta | (Phi) | P [comp x] A
parseTheta :: [TknPOCTL] -> [Int] -> (POCTL, [TknPOCTL])
parseTheta (Ttrue:tkns) _   = (VerdadP, tkns)
parseTheta (Ffalse:tkns) _  = (FalsoP, tkns)
parseTheta (AProp str:tkns) _ = (AtomP str, tkns)
parseTheta (LeftPar:tkns) bs  = let (phi, left) = parsePhi tkns bs 
                                in case left of
                                (RightPar:rmndr) -> (phi, rmndr)
                                _                -> error "Failure since there is a missing closing parenthesis"
parseTheta (LogOp Neg:tkns) bs = let (theta, left) = parseTheta tkns bs
                                 in (NoP theta, left)                               
parseTheta (ProbOp
            :LeftSqBrckt
            :Comp c
            :Range x
            :RightSqBrckt
            :tkns) bs = if 0<=x && x<=1 
                        then let (path, rmndr) = parsePathA tkns bs
                             in (Prob c x path, rmndr) 
                        else error "The number that is used to define the probability range is not a number between 0 and 1."

-- Now, we will parse path formulas according to the grammar 
--      A ::= B | B v A
--      B ::= C | C ^ B
--      C ::= D | D U C
--      D ::= E | E U n D
--      E ::= ~E | (A) | X_{obs} E | Theta
-- Next we'll parse the grammatical cathegory A ::= B | B v A 
parsePathA :: [TknPOCTL] -> [Int] -> (PathF, [TknPOCTL])
parsePathA tkns bs = 
  case xs of
    (LogOp Disj):left   -> let (a, rmndr) = parsePathA left bs
                           in (OPath b a, rmndr)
    _                   -> (b, xs) 
  where
    (b, xs) = parsePathB tkns bs
    
-- Next we'll parse the grammatical cathegory B ::= C | C ^ B
parsePathB :: [TknPOCTL] -> [Int] -> (PathF, [TknPOCTL])
parsePathB tkns bs =
  case xs of
    (LogOp Conj):left   -> let (b, rmndr) = parsePathB left bs
                           in (YPath c b, rmndr)
    _                   -> (c, xs) 
  where
    (c, xs) = parsePathC tkns bs
    
-- Next we'll parse the grammatical cathegory C ::= D | D U C
parsePathC :: [TknPOCTL] -> [Int] -> (PathF, [TknPOCTL])
parsePathC tkns bs = 
  case xs of 
    (TempOp UntilO):left        -> let (c, rmndr) = parsePathC left bs                           
                                   in (UntilPath d c, rmndr)
    _                           -> (d, xs) 
  where
    (d, xs) = parsePathD tkns bs
    
-- Next we'll parse the grammatical cathegory D ::= E | E U n D
parsePathD :: [TknPOCTL] -> [Int] -> (PathF, [TknPOCTL])
parsePathD tkns bs =
  case xs of
    (TempOp UntilO
     :UBound n
     :left)        -> if n >= 0 
                      then let (d, rmndr) = parsePathD left bs
                           in (UntilBPath n e d, rmndr) 
                      else error "The bounded until operator is bounded by a negative number."
    _              -> (e, xs) 
  where
    (e, xs) = parsePathE tkns bs

-- Next we'll parse the grammatical cathegory E ::= ~E | (A) | X_{obs} E | Theta
parsePathE :: [TknPOCTL] -> [Int] -> (PathF, [TknPOCTL])
parsePathE (LogOp Neg:tkns) bs = let (e,rmndr) = parsePathE tkns bs                       
                                 in (NoPath e, rmndr)
parsePathE (LeftPar:tkns) bs = let (a, rmndr) = parsePathA tkns bs
                               in case rmndr of
                                 (RightPar):xs     -> (a, xs)
                                 _                 -> error "No closing parenthesis found."
parsePathE (TempOp NextO
            :Underscore
            :NextObs obs:tkns) bs = if subList (sort obs) bs 
                                    then let (e, rmndr) = parsePathE tkns bs
                                            in (NextPath obs e, rmndr)
                                    else error "The observations of the Next operator are invalid."
parsePathE tkns bs = let (theta, rmndr) = parseTheta tkns bs
                     in (FormP theta, rmndr)
                        
-- Auxiliary function that computes whether the first list is a sublist of the second one. Both lists are sorted.                        
subList :: Eq a => [a] -> [a] -> Bool                        
subList [] _ = True
subList _ [] = False
subList (x:xs) (y:ys) = if x==y  
                        then subList xs ys 
                        else subList (x:xs) ys
