module Text.Layout.Table.Spec.HeaderSpec where

import Data.Default.Class

import Text.Layout.Table.Spec.HeaderColSpec

-- | Specifies a header.
-- This includes a separator label to indicate the delimiter use between
-- columns, a '[HeaderColSpec]' specifying how to render each header column,
-- and the list of content for the header column.
-- The constructor NoneHS means that the header is not displayed, but that the
-- shape of the header is determined by the data within the body, and the
-- separator label sep is used.
data HeaderSpec sep a
    = HeaderHS sep [HeaderColSpec] [a]
    | NoneHS sep

-- | By the default the header is not shown.
instance Default sep => Default (HeaderSpec sep a) where
    def = NoneHS def

-- | Specify no header, with columns separated by a given separator.
noneSepH :: sep -> HeaderSpec sep String
noneSepH = NoneHS

-- | Specify no header, with columns separated by a default separator.
noneH :: HeaderSpec () String
noneH = noneSepH ()

-- | Specify a header column for every title, with a given separator.
fullSepH :: sep -> [HeaderColSpec] -> [a] -> HeaderSpec sep a
fullSepH = HeaderHS

-- | Specify a header column for every title, with a default separator.
fullH :: [HeaderColSpec] -> [a] -> HeaderSpec () a
fullH = fullSepH ()

-- | Use titles with the default header column specification and separator.
titlesH :: [a] -> HeaderSpec () a
titlesH = fullSepH () (repeat def)
