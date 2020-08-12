{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Nonogram where

import System.Environment
import Data.List
import Control.Monad.ST
import Data.Tuple
import Distribution.Simple.Utils
import Data.Array.IO
import Data.Array
import Data.Array.ST
import Control.Monad
import Control.Monad.Loops
import Data.Either
import Data.STRef
import qualified Data.ByteString.Char8 as C
import Debug.Trace
import Control.Monad.Trans.State
import Control.Arrow

type Overlap = ([(Int , Int)] , [(Int , Int)])
type Row = [Int]
type Col = [Int]
type Dim = Int
type Value = Maybe Bool
type Solution s = STArray s (Int , Int) Value


{- This solution does not guess; it uses strategy -}

--Todo : fix a better design/read for input files?
runSolve :: IO ()
runSolve = do str <- getArgs >>= C.readFile . head
              let [cs,rs] = C.split 'b' str
              let cols = fmap (fmap (Prelude.read . C.unpack) . C.words) (C.lines cs) :: [[Int]]
              let width = length cols
              let rows = fmap (fmap (Prelude.read . C.unpack) . C.words) (C.lines rs)
              let height = length rows
              putStrLn "Solution:"
              putStrLn (prettySolution (runSTArray (createSol (width , height) rows cols)))

-- Print the solution
prettySolution :: Array (Int , Int) Value -> String
prettySolution sol = unlines [[chr (sol ! (i , j)) | i <- [i0..i1]] | j <- [j0..j1]]
  where ((i0 , j0) , (i1 , j1)) = bounds sol
        chr Nothing = '.'
        chr (Just b) = if b then 'x' else ' '

-- Start the ST computation
createSol :: (Int , Int) -> [[Int]] -> [[Int]] -> ST s (STArray s (Int , Int) Value)
createSol dim@(w , h) rs cs = do sol <- newArray ((1 , 1) , dim) Nothing
                                 ovrs <- newListArray (1 , h) (fmap (initOverlap w) rs)
                                 ovcs <- newListArray (1 , w) (fmap (initOverlap h) cs)
                                 solve ovrs ovcs sol
                                 return sol

-- Create the inital overlap ranges
initOverlap :: Dim -> [Int] -> Overlap
initOverlap d rs = (min , max)
                   where min = reverse (overlap rs [])
                         max = reverse (overlap (reverse rs) [])

-- Fit [Int] in the minimal way
overlap :: [Int] -> [(Int , Int)] -> [(Int , Int)]
overlap [] y = y
overlap (x:xs) [] = overlap xs [(1 , x)]
overlap (x:xs) (y@(y0 , y1):ys) = overlap xs ((y1 + 2 , y1 + 1 + x):y:ys)

-- Continue updating, untill all squares have been filled
-- It is unsure whether the strategy will solve any Nonogram
-- Might be better to include some 'untill it does not change' clause instead
solve :: STArray s Int Overlap -> STArray s Int Overlap -> Solution s -> ST s ()
solve rs cs sol = whileM_ (any null <$> getElems sol) $ do applyOverlap True rs sol
                                                           updateOverlap False cs sol
                                                           applyOverlap False cs sol
                                                           updateOverlap True rs sol

-- we use int for the bounds within the Array
-- we use ext to talk about the bound in the other direction
-- Fill in squares that overlap
-- Make squares blank that are unreachable
applyOverlap :: Bool -> STArray s Int Overlap -> Solution s -> ST s ()
applyOverlap b xs sol = do (_ , bds) <- getBounds sol
                           let (int , ext) = orient b bds
                           forM_ [1..ext] (\n -> do
                                                x <- readArray xs n
                                                forM_ (combine int x) (\((_ , minr) , (maxl , _)) -> forM_ [maxl..minr] (\k -> writeArray sol (orient b (k , n)) (Just True)))
                                                forM_ (findDots int (((0,0),(0,0)) : combine int x)) (\(l,r) -> forM_ [l..r] (\k -> writeArray sol (orient b (k , n)) (Just False))))

-- Find the squares that are unreachable
findDots :: Dim -> [((Int , Int) , (Int , Int))] -> [(Int,Int)]
findDots d [] = []
findDots d [((_ , _) , (_ , maxr))] = [(maxr + 1 , d)]
findDots d (((_ , _) , (_ , maxr)):x@((minl , _) , (_ , _)):xs) = (maxr + 1 , minl - 1) : findDots d (x:xs)

-- Deal with orientation. Can this be improved?
orient :: Bool -> (a , a) -> (a , a)
orient b pair = if b then pair else swap pair

-- Translate something from r->l to l->r
translate :: Dim -> Int -> Int
translate d k = d + 1 - k

-- Combines overlap into a comparable format
combine :: Dim -> Overlap -> [((Int , Int) , (Int , Int))]
combine d (min , max) = zip min (reverse (fix max))
                      where fix [] = []
                            fix ((l , r):xs) = (translate d r , translate d l) : fix xs

-- Update the overlap to adjust for the filled in values
updateOverlap :: Bool -> STArray s Int Overlap -> Solution s -> ST s ()
updateOverlap b xs sol = do (_ , bds) <- getBounds sol
                            let (int , ext) = orient b bds
                            vals <- getAssocs sol
                            forM_ [1..ext] (\n -> do x <- readArray xs n
                                                     let xvals = [(i , b') | (pos , Just b') <- vals , let (i , e) = orient b pos , e == n]
                                                     let xvals' = reverse (fmap (first (translate int)) xvals)
                                                     let y = (adjust xvals *** adjust xvals') x
                                                     writeArray xs n y)

-- Find the first possible minimal adjustment, that fits the spacing, and matches the constraints.
-- There must(!) exist a unique such one, if the puzzle is solvable
-- This heavily uses lazy evalution
adjust :: [(Int , Bool)] -> [(Int , Int)] -> [(Int , Int)]
adjust cs os = head $ filter (matches cs) $ zipWith (\(m , n) k -> (m + k , n + k)) os <$> tweaks (spacing os) [replicate (length os) 0]

-- Check whether the presented possibility matches the constrains
matches :: [(Int , Bool)] -> [(Int , Int)] -> Bool
matches [] es = True
matches cs [] = all (not . snd) cs
matches c@((pos , b):cs) e@((l , r):es) | pos < l = not b && matches cs e
                                | pos > r = matches c es
                                | otherwise = b && matches cs e

-- Find the distance between consecutive blocks
spacing :: [(Int , Int)] -> [Int]
spacing [] = []
spacing [(_ , r)] = []
spacing ((_ , r):x@((l , _):xs)) = l - r - 2 : spacing x

-- List of possible adjustments, ordered by number of steps
-- Be aware that this function does not terminate, as it is not bounded by a dimension
-- The use of ordNub drastically reduces the number of elements
tweaks :: [Int] -> [[Int]] -> [[Int]]
tweaks ss xs = xs ++ tweaks ss (ordNub $ join $ fmap (addone ss) xs)

-- Given an adjustment, produce those with one additional step allowed
-- Only produces allowed adjustments
addone :: [Int] -> [Int] -> [[Int]]
addone _ [] = []
addone _ [t] = [[t+1]]
addone (s:ss) (t:t':ts) | t - t' < s = (t + 1:t':ts) : fmap (t:) (addone ss (t':ts))
                        | otherwise = fmap (t:) (addone ss (t':ts))
