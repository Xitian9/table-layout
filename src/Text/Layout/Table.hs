-- | This module provides tools to layout text as grid or table. Besides basic
-- things like specifying column positioning, alignment on the same character
-- and length restriction it also provides advanced features like justifying
-- text and fancy tables with styling support.
--
{-# LANGUAGE RecordWildCards #-}
module Text.Layout.Table
    ( -- * Layout combinators
      -- | Specify how a column is rendered with the combinators in this
      -- section. Sensible default values are provided with 'def'.

      module Data.Default.Class

      -- ** Columns
    , ColSpec
    , column
    , numCol
    , fixedCol
    , fixedLeftCol
      -- ** Length of columns
    , LenSpec
    , expand
    , fixed
    , expandUntil
    , fixedUntil
      -- ** Positional alignment
    , Position
    , H
    , left
    , right
    , center
      -- ** Alignment of cells at characters
    , AlignSpec
    , noAlign
    , charAlign
    , predAlign
    , dotAlign
      -- ** Cut marks
    , CutMark
    , noCutMark
    , singleCutMark
    , doubleCutMark

      -- * Basic grid layout
    , Row
    , grid
    , gridLines
    , gridString
    , concatRow
    , concatLines
    , concatGrid

      -- * Grid modification functions
    , altLines
    , checkeredCells

      -- * Table layout
      -- ** Grouping rows
    , RowGroup
    , rowsG
    , rowG
    , colsG
    , colsAllG

      -- ** Headers
    , HeaderColSpec
    , headerColumn
    , HeaderSpec
    , fullH
    , titlesH

      -- ** Layout
    , tableLines
    , tableString

      -- * Text justification
      -- $justify
    , justify
    , justifyText

      -- * Vertical column positioning
    , Col
    , colsAsRowsAll
    , colsAsRows
    , top
    , bottom
    , V

      -- * Table styles
    , module Text.Layout.Table.Style

      -- * Column modification functions
    , pad
    , trimOrPad
    , align
    , alignFixed

      -- * Column modifaction primitives
      -- | These functions are provided to be reused. For example if someone
      -- wants to render their own kind of tables.
    , ColModInfo
    , widthCMI
    , unalignedCMI
    , ensureWidthCMI
    , ensureWidthOfCMI
    , columnModifier
    , AlignInfo
    , widthAI
    , deriveColModInfos
    , deriveAlignInfo
    , OccSpec
    ) where

-- TODO AlignSpec:   multiple alignment points - useful?
-- TODO RowGroup:    optional: vertical group labels
-- TODO RowGroup:    optional: provide extra layout for a RowGroup
-- TODO ColSpec:     add some kind of combinator to construct ColSpec values (e.g. via Monoid, see optparse-applicative)

import           Data.List
import           Data.Default.Class
import           Data.Default.Instances.Base                 ()

import           Text.Layout.Table.Cell
import           Text.Layout.Table.Justify
import           Text.Layout.Table.Primitives.AlignInfo
import           Text.Layout.Table.Primitives.Basic
import           Text.Layout.Table.Primitives.ColumnModifier
import           Text.Layout.Table.Primitives.Header
import           Text.Layout.Table.Primitives.Table
import           Text.Layout.Table.Spec.AlignSpec
import           Text.Layout.Table.Spec.ColSpec
import           Text.Layout.Table.Spec.CutMark
import           Text.Layout.Table.Spec.HeaderColSpec
import           Text.Layout.Table.Spec.HeaderSpec
import           Text.Layout.Table.Spec.LenSpec
import           Text.Layout.Table.Spec.OccSpec
import           Text.Layout.Table.Spec.Position
import           Text.Layout.Table.Spec.RowGroup
import           Text.Layout.Table.Spec.Util
import           Text.Layout.Table.StringBuilder
import           Text.Layout.Table.Style
import           Text.Layout.Table.Vertical

-------------------------------------------------------------------------------
-- Layout types and combinators
-------------------------------------------------------------------------------

-- | Align all text at the first dot from the left. This is most useful for
-- floating point numbers.
dotAlign :: AlignSpec
dotAlign = charAlign '.'

-- | Numbers are positioned on the right and aligned on the floating point dot.
numCol :: ColSpec
numCol = column def right dotAlign def

-- | Fixes the column length and positions according to the given 'Position'.
fixedCol :: Int -> Position H -> ColSpec
fixedCol l pS = column (fixed l) pS def def

-- | Fixes the column length and positions on the left.
fixedLeftCol :: Int -> ColSpec
fixedLeftCol i = fixedCol i left

-------------------------------------------------------------------------------
-- Basic layout
-------------------------------------------------------------------------------

-- | Modifies cells according to the column specification.
grid :: Cell a => [ColSpec] -> [Row a] -> [Row String]
grid specs tab = zipWith ($) (deriveColMods specs tab) <$> tab

-- | Behaves like 'grid' but produces lines by joining with whitespace.
gridLines :: Cell a => [ColSpec] -> [Row a] -> [String]
gridLines specs = fmap unwords . grid specs

-- | Behaves like 'gridLines' but produces a string by joining with the newline
-- character.
gridString :: Cell a => [ColSpec] -> [Row a] -> String
gridString specs = concatLines . gridLines specs

concatLines :: StringBuilder b => [b] -> b
concatLines = mconcat . intersperse (charB '\n')

-- | Concatenates a row with a given amount of spaces.
concatRow
    :: StringBuilder b
    => Int
    -> Row b
    -> b
concatRow n bs = mconcat $ intersperse (replicateCharB n ' ') bs

concatGrid :: StringBuilder b => Int -> [Row b] -> b
concatGrid n = concatLines . fmap (concatRow n)

-------------------------------------------------------------------------------
-- Grid modification functions
-------------------------------------------------------------------------------

-- | Applies functions to given lines in a alternating fashion. This makes it
-- easy to color lines to improve readability in a row.
altLines :: [a -> b] -> [a] -> [b]
altLines = zipWith ($) . cycle

-- | Applies functions to cells in a alternating fashion for every line, every
-- other line gets shifted by one. This is useful for distinguishability of
-- single cells in a grid arrangement.
checkeredCells  :: (a -> b) -> (a -> b) -> [[a]] -> [[b]]
checkeredCells f g = zipWith altLines $ cycle [[f, g], [g, f]]

-------------------------------------------------------------------------------
-- Advanced layout
-------------------------------------------------------------------------------

-- | Create a 'RowGroup' by aligning the columns vertically. The position is
-- specified for each column.
colsG :: Monoid a => [Position V] -> [Col a] -> RowGroup a
colsG ps = rowsG . colsAsRows ps

-- | Create a 'RowGroup' by aligning the columns vertically. Each column uses
-- the same vertical positioning.
colsAllG :: Monoid a => Position V -> [Col a] -> RowGroup a
colsAllG p = rowsG . colsAsRowsAll p

-- | Layouts a pretty table with an optional header. Note that providing fewer
-- layout specifications than columns or vice versa will result in not showing
-- the redundant ones.
tableLines :: Cell a
           => [ColSpec]  -- ^ Layout specification of columns
           -> TableStyle -- ^ Visual table style
           -> HeaderSpec -- ^ Optional header details
           -> [RowGroup a] -- ^ Rows which form a cell together
           -> [String]
tableLines specs TableStyle { .. } header rowGroups =
    maybe id (:) optTopLine . addHeaderLines $ maybe id (\b -> (++[b])) optBottomLine rowGroupLines
  where
    -- Helpers for horizontal lines that will put layout characters arround and
    -- in between a row of the pre-formatted grid.

    -- | Generate columns filled with 'sym', or blank spaces if 'sym' is of width 0.
    fakeColumns sym = map replicateSym colWidths
      where
        replicateSym w = concat $ replicate q sym' ++ [take r sym']
          where
            (q, r) = w `quotRem` l
        (sym', l) = let l' = length sym in if l' == 0 then (" ", 1) else (sym, l')

    -- Horizontal seperator lines that occur in a table.
    optTopLine       = optHorizontalDetailLine realTopH realTopL realTopC realTopR $ fakeColumns realTopH
    optBottomLine    = optHorizontalDetailLine groupBottomH groupBottomL groupBottomC groupBottomR $ fakeColumns groupBottomH
    optGroupSepLine  = optHorizontalDetailLine groupSepH groupSepLC groupSepC groupSepRC $ fakeColumns groupSepH
    optHeaderSepLine = optHorizontalDetailLine headerSepH headerSepLC headerSepC headerSepRC $ fakeColumns headerSepH

    -- Vertical content lines
    rowGroupLines = maybe concat (\seps -> intercalate [seps]) optGroupSepLine linesPerRowGroup
    linesPerRowGroup = map rowGroupToLines rowGroups
    rowGroupToLines = map (horizontalContentLine groupV) . applyRowMods . rows

    -- Optional values for the header
    (addHeaderLines, fitHeaderIntoCMIs, realTopH, realTopL, realTopC, realTopR)
                  = case header of
        HeaderHS headerColSpecs hTitles
               ->
            let headerLine    = horizontalContentLine headerV (zipWith ($) headerRowMods hTitles)
                headerRowMods = zipWith3 headerCellModifier
                                         headerColSpecs
                                         cMSs
                                         cMIs
            in
            ( (headerLine :) . maybe id (:) optHeaderSepLine
            , fitTitlesCMI hTitles posSpecs
            , headerTopH
            , headerTopL
            , headerTopC
            , headerTopR
            )
        NoneHS ->
            ( id
            , id
            , groupTopH
            , groupTopL
            , groupTopC
            , groupTopR
            )

    cMSs          = map cutMark specs
    posSpecs      = map position specs
    applyRowMods  = map (zipWith ($) rowMods)
    rowMods       = zipWith3 columnModifier posSpecs cMSs cMIs
    cMIs          = fitHeaderIntoCMIs $ deriveColModInfos' specs $ concatMap rows rowGroups
    colWidths     = map widthCMI cMIs

-- | Does the same as 'tableLines', but concatenates lines.
tableString :: Cell a
            => [ColSpec]  -- ^ Layout specification of columns
            -> TableStyle -- ^ Visual table style
            -> HeaderSpec -- ^ Optional header details
            -> [RowGroup a] -- ^ Rows which form a cell together
            -> String
tableString specs style header rowGroups = concatLines $ tableLines specs style header rowGroups

-------------------------------------------------------------------------------
-- Text justification
-------------------------------------------------------------------------------

-- $justify
-- Text can easily be justified and distributed over multiple lines. Such
-- columns can be combined with other columns.
