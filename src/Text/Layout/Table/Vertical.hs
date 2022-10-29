-- | This module provides functions for vertical alginment of columns.
module Text.Layout.Table.Vertical
    ( -- * Vertical padding of columns
      vPad
    , vPadAll
    , -- * Converting columns to rows with positioning
      colsAsRowsAll
    , colsAsRows
    ) where

import Data.List

import Text.Layout.Table.Cell
import Text.Layout.Table.Spec.Position
import Text.Layout.Table.Spec.Util
import Text.Layout.Table.Primitives.Basic

{- | Merges multiple columns together to a valid grid without holes. For example:

>>> colsAsRowsAll top [justifyText 10 "This text will not fit on one line.", ["42", "23"]]
[["This  text","42"],["will   not","23"],["fit on one",""],["line.",""]]

The result is intended to be used with a grid layout function like 'Text.Layout.Table.grid'.
-}
colsAsRowsAll :: Cell a => Position V -> [Col a] -> [Row a]
colsAsRowsAll ps = transpose . vPadAll emptyCell ps

{- | Works like 'colsAsRowsAll' but every position can be specified on its
   own:

>>> colsAsRows [top, center, bottom] [["a1"], ["b1", "b2", "b3"], ["c3"]]
[["a1","b1",""],["","b2",""],["","b3","c3"]]
-}
colsAsRows :: Cell a => [Position V] -> [Col a] -> [Row a]
colsAsRows ps = transpose . vPad emptyCell ps

-- | Fill all columns to the same length by aligning at the given position.
vPadAll :: a -> Position V -> [Col a] -> [Col a]
vPadAll x = vPad x . repeat

-- | Fill all columns to the same length by aligning at the given positions.
vPad :: a -> [Position V] -> [Col a] -> [Col a]
vPad x vs l = zipWith fillToMax vs l
  where
    fillToMax vPos = fillTo vPos $ maximum $ 0 : fmap length l
    fillTo vPos    = let f = case vPos of
                            Start  -> fillEnd
                            Center -> fillBoth
                            End    -> fillStart
                     in f x
