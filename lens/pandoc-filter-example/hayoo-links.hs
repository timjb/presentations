{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

module Main where

import Control.Lens
import Control.Lens.Cons (unsnoc)
import Control.Lens.Plated (transformOf)
import Data.Aeson (encode, eitherDecode', Value)
import Data.Aeson.Lens
import qualified Data.ByteString.Lazy as BL
import Data.Char (isUpper, isLower, isAlphaNum)
import Data.Data.Lens (template)
import Data.List (intercalate)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import Data.Text.Lens (packed, unpacked)
import Network.Wreq
import Text.Pandoc

import System.IO (stderr, hPutStrLn)

data HsIdentifier
  = HsModule [String]
  | HsFunction [String] String
  deriving (Show, Eq)

parseHsIdentifier :: String -> Maybe HsIdentifier
parseHsIdentifier str =
  uncurry mkIdentifier =<< unsnoc (splitOn "." str)
  where
    mkIdentifier [] _ = Nothing
    mkIdentifier ms _
      | not (all validModuleName ms) = Nothing
    mkIdentifier ms m
      | validModuleName   m = Just $ HsModule $ ms ++ [m]
      | validFunctionName m = Just $ HsFunction ms m
    mkIdentifier _ _ = Nothing
    validModuleName "" = False
    validModuleName (c:cs) = isUpper c && all isAlphaNum cs
    validFunctionName "" = False
    validFunctionName (c:cs) = isLower c && all isAlphaNum cs

-- returns (str', url, title) pair
getIdentifierInfos :: HsIdentifier -> IO (Maybe (Maybe String, String, String))
getIdentifierInfos identifier = do
  let queryModule ms = "module:" ++ intercalate "." ms
      (str', query) =
        case identifier of
          HsModule   ms   -> (Nothing, queryModule ms)
          HsFunction ms f -> (Just f, queryModule ms ++ " " ++ f)
      opts = defaults & param "query" .~ [query^.packed]
  r <- getWith opts "http://hayoo.fh-wedel.de/json"
  let firstResult = r ^? responseBody . key "result" . nth 0
  return $ case firstResult of
    Nothing  -> Nothing
    Just res -> Just ( str'
                     , fromMaybe "" $ res ^? key "resultUri"       . _String . unpacked
                     , fromMaybe "" $ res ^? key "resultSignature" . _String . unpacked)

hayooLinkModules :: Inline -> IO Inline
hayooLinkModules code@(Code attr str) =
  case parseHsIdentifier str of
    Nothing -> return code
    Just identifier ->
      maybe code (\(str', url, title) -> Link [maybe code (Code attr) str'] (url, title))
        <$> getIdentifierInfos identifier
hayooLinkModules x = return x

main :: IO ()
main = pipeline $ traverseOf template hayooLinkModules
  where
    pipeline :: (Pandoc -> IO Pandoc) -> IO ()
    pipeline f = BL.putStr . encode =<<
                 f . either error id . eitherDecode' =<< BL.getContents
