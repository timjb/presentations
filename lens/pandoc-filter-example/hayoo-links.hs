module Main where

import Control.Lens (over)
import Control.Lens.Plated (transformOf)
import qualified Data.ByteString.Lazy as BL
import Data.Char (isUpper, isAlphaNum)
import Data.Data.Lens (template)
import Data.List.Split (splitOn)
import Data.Aeson (encode, eitherDecode')
import Text.Pandoc

isHaskellModule :: String -> Bool
isHaskellModule str =
  length components >= 2 && all validName components
  where
    components = splitOn "." str
    validName "" = False
    validName (c:cs) = isUpper c && all isAlphaNum cs

hayooLinkModules :: Inline -> Inline
hayooLinkModules code@(Code attr str)
  | isHaskellModule str = Link [code] (url, title)
  where
    url   = "http://hayoo.fh-wedel.de/?query=" ++ str
    title = "Hayoo: " ++ str
hayooLinkModules x = x

main :: IO ()
main = pipeline $ over template hayooLinkModules
  where
    pipeline :: (Pandoc -> Pandoc) -> IO ()
    pipeline f = BL.putStr . encode . f
                 . either error id . eitherDecode' =<< BL.getContents
