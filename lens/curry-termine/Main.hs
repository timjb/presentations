{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Monoid ((<>))
import Data.Text.IO as T
import Text.XML
import Text.XML.Lens
import Network.Wreq

main :: IO ()
main = do
  res <- get "http://curry-club-augsburg.de/atom.xml"
  forOf_ (responseBody . to (parseLBS def) . _Right . entryTitles)
         res
         (T.putStrLn . ("* " <>))
  where
    entryTitles = root . childEl "entry" . childEl "title" . text
    childEl tag = nodes . traverse . _Element . named tag
