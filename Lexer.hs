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

module Lexer(Token(..), WordRsv(..), TknPOCTL(..), ProLOp(..), TempOp(..), lexer, lexerPOCTL) where

import Data.Char

-- Aliases of some primitive types
type Atom   = String
type Obser  = [Int]
type States = Int

-- Datatype for the tokens in which the HMM is broken into
data Token = SetSt States -- No of states
             | SetObs Obser -- Set of observations
             | Rsv WordRsv -- Reserved words
             | ODef -- = symbol
             | Lista [Double] -- Transition probability matrix
             | ListDouble [Double] -- Observation matrix
             | ListAtom [[Atom]] -- Labelling function
               deriving Show                        
                        
-- Datatype for the tokens of POCTL*
data TknPOCTL = Ttrue 
              | Ffalse 
              | AProp Atom 
              | LogOp ProLOp -- Propositional logic operators
              | TempOp TempOp -- Temporal operators
              | Comp String -- Comparison operators
              | NextObs Obser -- observation attached to the next operator
              | Range Double -- The treshold of the probabilistic operator
              | UBound Int -- The integer number that bounds the Unitl operator
              | ProbOp
              | LeftPar 
              | RightPar 
              | LeftSqBrckt
              | RightSqBrckt 
              | Underscore 
              deriving Show

-- Datatype for logical operators
data ProLOp = Neg | Conj | Disj deriving Show

-- Datatype for temporal operators
data TempOp = NextO | UntilO deriving Show

-- Datatype for the tokens of reserved words
data WordRsv = St | Trans | Lbl | Obs | ObsProb | IniDist 
             deriving Show
                      
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- This function takes a string, i.e., a file with the elements of an HMM, and returns
-- the list of tokens that make up the HMM   
lexer :: String -> [Token]
lexer "" = []
lexer (c:left) | isSpace c = lexer left
lexer ('=':rmndr) = ODef : lexer rmndr

-- We're about to read a reserved word or a integer that 
-- represents the number of states
lexer (c:left) 
  | isAlpha c = lexIdRsv (c:left)
  | isDigit c = SetSt (read tmp::Int) : lexer newLeft    
  where 
    (tmp, newLeft) = break (not . isDigit) (c:left)
    
-- We're about to read the set of observations 
lexer ('"':rmndr) = SetObs [1..(read tmp)] : lexer newRmndr 
  where
    (tmp, xs) = break (=='"') rmndr
    newRmndr  = if null xs 
                then error "Unable to generate token. Problem reading the number of observations." 
                else tail xs
    
-- Now we read the labelling function
lexer ('[':'[':'"':remainder) = ListAtom lst : lexer newRemainder 
  where
    (lst, xs) = getLbls ('"':remainder)
    newRemainder = if length xs < 2 
                   then error "Unable to generate token. Problem reading the set of atomic propositions for each state." 
                   else tail (tail xs)
                        
-- This is the case where we read the matrix of double values
lexer ('[':'[':left) = ListDouble token : lexer newLeft 
  where 
    (token, xs) =  doubleVals left
    newLeft = if length xs < 2 
              then error "Unable to generate token. Problem reading the matrix of double values." 
              else tail (tail xs)

-- Finally, we read the initial distribution vector of double double values
lexer ('[':rmndr) = Lista (doubleSimple token) : lexer newRmndr 
  where 
    (token, xs) = break (==']') rmndr
    newRmndr = if null xs 
               then error "Unable to generate token. Problem reading the initial probability values." 
               else tail xs
lexer _ = error "Unrecognizable token."  



-- This function takes a string representing a  matrix of the form ..], [..], .., [..]]
-- of double values and returns the corresponding list of all double values
doubleVals :: String -> ([Double], String)
doubleVals list = if (head (tail aux2)==']') 
                  then (res,aux2) 
                  else (res ++ tmp1, tmp2) 
  where    
    (aux1,aux2) =  break (==']') list   
    res = doubleList aux1
    (tmp1,tmp2) = doubleVals (tail aux2)
    
-- With this functions we identify a list of doubles from a string [..
doubleList :: String -> [Double]
doubleList [] = []
doubleList (',':left) = doubleList left 
doubleList (c:left) | isSpace c = doubleList left
doubleList ('[':left) = doubleList left
doubleList left = 
  if null sndPart 
  then (read (num1)::Double):doubleList leftL  
  else if (head sndPart=='.') 
       then let (num2, _) = break (not . isDigit) (tail sndPart) 
            in (read (num1++"."++num2)::Double):doubleList leftL 
       else error "Problem while reading the transition probability matrix." 
  where
    (tmp, leftL) = break (\x-> x==',') left
    (fstPart,sndPart) = break (\x-> x=='.' || not(isDigit x)) tmp
    num1 = if null fstPart
           then "0" 
           else fstPart 
    
-- This function takes a string of the form x, x,.., x] and 
-- returns the list of double produced by it
doubleSimple :: String -> [Double]
doubleSimple [] = []
doubleSimple (',':rmndr) = doubleSimple rmndr 
doubleSimple (c:rmndr) | isSpace c = doubleSimple rmndr
doubleSimple rmndr = 
  if null sndPart 
  then (read (num1)::Double):doubleSimple rmndrL  
  else if (head sndPart=='.') 
       then let (num2, _) = break (not . isDigit) (tail sndPart) 
            in (read (num1++"."++num2)::Double):doubleSimple rmndrL 
       else error "Problem while reading the initial distribution vector." 
  where
    (tmp, rmndrL) = break (\x-> x==',') rmndr
    (fstPart,sndPart) = break (\x-> x=='.' || not(isDigit x)) tmp
    num1 = if null fstPart 
           then "0" 
           else fstPart 

-- With this function we obtain the list of observations (strings) assigned to 
-- each state. 
-- Its input is a string of the form "str", "str", .., "str"], ["str", "str", .., "str"], .., ["str", "str", .., "str"]]
getLbls :: String -> ([[Atom]], String)
getLbls list = if (head (tail aux2) == ']') 
               then (res:[], aux2) 
               else (res:tmp1, tmp2) 
  where
    (aux1, aux2) = break (==']') list
    res = parseStrings aux1
    (tmp1, tmp2) = getLbls (tail aux2)

-- This auxiliary function takes a string of the form [".. ", "..", .., ".."] and returns
-- a list of strings
parseStrings :: String -> [String]
parseStrings [] = []
parseStrings (',':rmndr) = parseStrings rmndr 
parseStrings (c:rmndr) | isSpace c = parseStrings rmndr 
parseStrings ('[':rmndr) = parseStrings rmndr
parseStrings ('"':rmndr) | null myLst  = error "Problem while reading labels, no closing \" (quotation mark)"
                         | otherwise   = atom : parseStrings (tail myLst)    
  where
    (atom, myLst) = break (=='"') rmndr
parseStrings _ = error "Problem while reading labels."

-- With the next function we recognized reserved words
lexIdRsv :: String -> [Token]
lexIdRsv xs =
  let (name, left) = break (not . isAlpha) xs
      token        = case name of 
        "States"        -> Rsv St
        "Transitions"   -> Rsv Trans
        "Labelling"     -> Rsv Lbl
        "Observations"  -> Rsv Obs 
        "ObsProb"       -> Rsv ObsProb
        "Initial"       -> Rsv IniDist 
        _               -> error "No reserved word"
  in token : lexer left
     

-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- This function returns a list of tokens taken out  
-- of a string representing a POCTL* formula
lexerPOCTL :: String -> [TknPOCTL]
lexerPOCTL "" = []
lexerPOCTL (c:left) | isSpace c = lexerPOCTL left
lexerPOCTL ('(':rmndr) = LeftPar  : (lexerPOCTL rmndr)
lexerPOCTL (')':rmndr) = RightPar : (lexerPOCTL rmndr)
lexerPOCTL ('[':left)  = LeftSqBrckt : (lexerPOCTL left)
lexerPOCTL (']':left)  = RightSqBrckt: (lexerPOCTL left)
lexerPOCTL ('v':left)  = LogOp Disj  : (lexerPOCTL left)
lexerPOCTL ('^':left)  = LogOp Conj  : (lexerPOCTL left)
lexerPOCTL ('~':left)  = LogOp Neg   : (lexerPOCTL left)
lexerPOCTL ('X':rmndr) = TempOp NextO : (lexerPOCTL rmndr)
lexerPOCTL ('U':rmndr) = TempOp UntilO: (lexerPOCTL rmndr)
lexerPOCTL ('T':rmndr) = Ttrue : lexerPOCTL rmndr
lexerPOCTL ('F':rmndr) = Ffalse : lexerPOCTL rmndr
lexerPOCTL ('P':rmndr) = ProbOp : lexerPOCTL rmndr
lexerPOCTL ('<':'=':left) = Comp "<=" : lexerPOCTL left
lexerPOCTL ('<':left) = Comp "<" : lexerPOCTL left
lexerPOCTL ('>':'=':left) = Comp ">=" : lexerPOCTL left
lexerPOCTL ('>':left) = Comp ">" : lexerPOCTL left
lexerPOCTL ('_':rmndr) = Underscore : lexerPOCTL rmndr
lexerPOCTL (c:rmndr) | isDigit c = lexDoubleInt (c:rmndr) 
                     | isAlpha c = lexAtom (c:rmndr)
lexerPOCTL ('{':rmndr) = if null aux2
                         then error "Not closing bracket for the set of observations."
                         else NextObs (toIntList aux1) : (lexerPOCTL (tail aux2)) 
  where
    (aux1, aux2) 	= break (=='}') rmndr
    toIntList [] 	= []
    toIntList (',':xs)	= toIntList xs
    toIntList xs	= let (tmp1, tmp2) = break (not . isDigit) xs
                          in (read tmp1):toIntList tmp2
lexerPOCTL _ = error "Unrecognizable symbol."



-- This function takes a string with a digit in its begining and
-- returns the corresponding TknPOCTL, which is either an integer  
-- that bounds the until operator (UBound n) or a double (format #.#) value 
-- that defines the probability range in the probability operator
lexDoubleInt :: String -> [TknPOCTL]
lexDoubleInt xs = if not (null aux2)
                  then if (head aux2 == '.') 
                       then let (tmp1, tmp2) = break (not . isDigit) (tail aux2) 
                            in Range (read (aux1++"."++tmp1)) : lexerPOCTL tmp2
                       else UBound (read aux1) : lexerPOCTL aux2
                  else UBound (read aux1) : lexerPOCTL aux2
  where
    (aux1, aux2) = break (not.isDigit) xs
    
-- A string that is not an operator nor a special character is 
-- an atomic proposition. This function recognizes atomic propositions.
lexAtom ys = AProp aux1 : lexerPOCTL aux2 
  where
    (aux1, aux2) = break (\x-> not(isAlpha x) || isReserved x) ys 
    
-- This function determines if it's input is a reserved symbol
isReserved :: Char -> Bool 
isReserved c = c=='v' || c=='X' || c=='U' || c=='P' || c=='T' || c=='F'