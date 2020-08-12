{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module SlowNonogram where

import System.Environment
import Data.List
import Control.Monad.ST
import Data.Array.IO
import Data.Array
import Data.Array.ST
import Control.Monad
import Data.Either
import Data.STRef
import qualified Data.ByteString.Char8 as C
import Debug.Trace
import Control.Monad.Trans.State

type Row = [Int]
type Column = [Int]
type Columns s = STArray s Int Column
type Fit = (Int,Int)
type Constr = [(Int,Bool)]
type Dim = Int


runSolve :: IO ()
runSolve = do str <- getArgs >>= C.readFile . head
              putStrLn "Solution:"
              putStrLn (printSolution (reverse (runST (createSol str))))

--Todo : fix a better design/read for input files
createSol :: C.ByteString -> ST s [[Fit]]
createSol str = do let (cs:rs:[]) = C.split 'b' str
                   let cols = fmap (fmap (Prelude.read . C.unpack) . C.words) (C.lines cs) :: [[Int]]
                   -- traceM (show cols)
                   let dimension = length cols
                   -- traceM (show dimension)
                   carray <- newListArray (0,dimension - 1) cols :: ST s (Columns s)
                   -- x <- freeze carray
                   -- traceM (show (x :: Array Int Column))
                   let rows = fmap (fmap (Prelude.read . C.unpack) . C.words) (C.lines rs) :: [[Int]]
                   -- traceM (show rows)
                   ref <- newSTRef []
                   solve dimension [] carray rows [] ref
                   readSTRef ref


printSolution :: [[Fit]] -> String
printSolution = unlines . fmap (printrow 0)
                   where printrow :: Int -> [Fit] -> String
                         printrow n [] = []
                         printrow n ((pos,len):rs) | n < pos = ' ':(printrow (n + 1) ((pos,len):rs))
                                                   | otherwise = replicate len 'x' ++ printrow (n + len) rs


-- In the second clause, we know for sure that n < d
-- In the third clause, we know for sure that the recursive calls are non-empty
-- Observation: Each [Fit] is ordered wrt first component
posFits :: Row -> Dim -> [[Fit]]
posFits [] d = [[]]
posFits [n] d = [[(x,n)] | x <- [0..(d-n)]]
posFits (n:(k:ns)) d = join (map (\fs -> [(x,n):fs | x <- [0..(fst (head fs) - n - 1)]]) (posFits (k:ns) d))

checkConstr :: [Fit] -> Constr -> Bool
checkConstr fs [] = True
checkConstr [] cs = all (not . snd) cs
checkConstr (f:fs) (c:cs) | fst c < fst f = not (snd c) && checkConstr (f:fs) cs
                           | fst f + snd f - 1 < fst c = checkConstr fs (c:cs)
                           | otherwise = snd c && checkConstr (f:fs) cs

-- When a [Fit] has been assigned, update the columns
-- We know for sure that [Fit] is compatible with Columns
-- We also know that all non-empty collumns do not start with a zero
updateColumn :: [Fit] -> Columns s -> ST s ()
updateColumn fs cs = forM_ fs (\f -> forM_ [fst f..fst f + snd f - 1] (\x -> do val <- readArray cs x
                                                                                writeArray cs x (head val - 1 : tail val)))


-- This function is under the assumption the [fit] passes the previous constrain:
-- This ensures that there can be no conflict with it, and the updated Columns
buildConstr :: Int -> [Fit] -> Columns s -> ST s Constr
buildConstr pos [] cs = do cs' <- getAssocs cs
                           return [(x,False) | (x,c) <- cs', x >= pos , null c]
buildConstr pos f@((loc,length):fs) cs | pos < loc = do c <- readArray cs pos
                                                        re <- buildConstr (pos + 1) f cs
                                                        if (null c)
                                                          then return ((pos,False):re)
                                                          else return re
                                        | pos == loc + length - 1 = do c <- readArray cs pos
                                                                       re <- buildConstr (pos + 1) fs cs
                                                                       return ((pos,not(head c == 0)):re)
                                        | otherwise =  do c <- readArray cs pos
                                                          re <- buildConstr (pos + 1) f cs
                                                          return ((pos,not(head c == 0)):re)

removeZeros :: Dim -> Columns s -> ST s ()
removeZeros d cs = forM_ [0..d-1] (\pos -> do c <- readArray cs pos
                                              writeArray cs pos (dummy c))
                 where dummy (0:xs) = xs
                       dummy xs = xs


solve :: Dim -> Constr -> Columns s -> [Row] -> [[Fit]] -> STRef s [[Fit]] -> ST s ()
solve d constr cs [] sol ref =  writeSTRef ref sol
solve d constr cs (r:rs) sol ref = {-traceM (show sol) >>-} forM_ (posFits r d) (\f -> when (checkConstr f constr) $ do cs' <- copyCols d cs
                                                                                                                        updateColumn f cs'
                                                                                                                        -- x <- freeze cs'
                                                                                                                        -- traceM (show (x :: Array Int Column))
                                                                                                                        constr' <- buildConstr 0 f cs'
                                                                                                                        -- traceM (show constr')
                                                                                                                        removeZeros d cs'
                                                                                                                        -- y <- freeze cs'
                                                                                                                        -- traceM (show (y :: Array Int Column))
                                                                                                                        solve d constr' cs' rs (f:sol) ref)

copyCols :: Dim -> Columns s -> ST s (Columns s)
copyCols d cs = do cs' <- newArray (0,d-1) []
                   forM_ [0..d-1] (\n -> readArray cs n >>= writeArray cs' n)
                   return cs'
