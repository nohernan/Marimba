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

module Main where 

import System.IO
import Parser
import Lexer
import ModelChecker
import DirectApproach
import Courcoubetis
import Data.Array

yesno :: String -> IO Bool
yesno prompt = 
  do
    putStr (prompt ++ " y/n: ")
    hFlush stdout
    str <- getLine
    case str of
      "y" -> return True
      "n" -> return False
      _   -> do 
        putStrLn "Invalid input."              
        yesno prompt

getPOCTLFormula :: HMM -> IO ()
getPOCTLFormula hmm = 
  do
    putStrLn "\nEnter the POCTL* formula we are interested in."
    poctlF <- getLine
    let formulaTokens = lexerPOCTL poctlF 
    
    let poctlFormula = parsePOCTL formulaTokens (obsHMM hmm)
    
    --putStr "\n"
    --print poctlFormula
    --putStr "\n"
    
    putStrLn "\nThe states that satisfy it are:"
    print (satPOCTL hmm poctlFormula)
    continue <- yesno "\nDo you want to continue checking more specifications?"
    if continue 
      then getPOCTLFormula hmm 
      else return ()

main :: IO ()
main = 
  do      
    hSetBuffering stdin NoBuffering
    putStrLn ""
    putStrLn "Marimba  Copyright (C) 2014  Noe Hernandez"
    putStrLn "This program comes with ABSOLUTELY NO WARRANTY. This is free software,"
    putStrLn "and you are welcome to redistribute it under certain conditions."
    putStrLn "For details see the COPYING file enclosed with the source code." 
    putStrLn ""
    putStrLn "Enter the file name where the HMM is located."
    
    fname    <- getLine                -- Reads the file name
    contents <- readFile fname         -- Reads the contents of the file
    
    let tokens = lexer contents
    
    answer <- yesno "\nWould you like to consider each state as if it were the initial\nstate, i.e., as if it had initial distribution value equal to 1?"
    
    let hmm = parse tokens answer
    
    getPOCTLFormula hmm
