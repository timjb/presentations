{-# LANGUAGE LambdaCase #-}

module Main where

import Graphics.Gloss.Interface.Pure.Game
import Graphics.Gloss.Data.Bitmap (loadBMP)
import Control.Lens
import Control.Monad.State.Lazy
import Control.Monad.Cont
import Control.Monad.Trans.Class
import Data.Maybe (fromMaybe)
import Paths_flappy_cat

import FlappyCat

main :: IO ()
main = do
  let load img = loadBMP =<< getDataFileName img
  socke      <- load "socke-klein.bmp"
  background <- load "socke-background.bmp"
  wfda       <- load "was-ficht-dich-an.bmp"
  let renderHandler = render socke background wfda
      inputHandler  = execFlappyMonad . handleInput
      stepHandler   = execFlappyMonad . step
  play displayMode white fps initialFlappyCat
    renderHandler inputHandler stepHandler
  where
    displayMode = InWindow "Flappy Cat" windowSize windowPos
    windowSize = (width, height)
    windowPos = (10, 10)
    fps = 50

render
  :: Picture -- ^ Socke
  -> Picture -- ^ Background
  -> Picture -- ^ Schnurrli, was ficht dich an?
  -> FlappyCat
  -> Picture
render socke background wfda fc
  | fc ^. gameState == GameOver =
      Pictures
      [ Translate (-110) (-150) $ Scale 0.3 0.3 $ Text "Game Over"
      , Translate 0 20 $ wfda
      , Color black $ Translate (-290) 170 $ Scale 0.15 0.15 $
          Text $ show $ round $ fc^.catPos.x
      ]
  | otherwise =
      Pictures
      [ background
      , Translate (-200) 0 $ Color darkBrown $
          Pictures $ fc ^.. hurdles.traverse.to renderHurdle
      , Translate (-200) (fc^.catPos.y) $ Rotate (catSlope fc * (180/pi)) socke
      , Color white $ Translate (-290) 170 $ Scale 0.15 0.15 $
          Text $ show $ round $ fc^.catPos.x
      ]
  where
    darkBrown = dim $ dim $ dim $ dim orange
    renderHurdle hurdle =
      let hx = hurdle^.hurdlePos.x - fc^.catPos.x
          rectPath y1 y2 = [(hx-25,y1), (hx+25,y1), (hx+25,y2), (hx-25,y2)]
          hy = hurdle^.hurdlePos.y
      in Pictures
         [ Polygon $ rectPath (-200) (hy - 70)
         , Polygon $ rectPath (hy + 70) 200
         ]

type FlappyMonad = ContT () (State FlappyCat)

abort :: FlappyMonad ()
abort = ContT $ const $ return ()

execFlappyMonad :: FlappyMonad () -> FlappyCat -> FlappyCat
execFlappyMonad = execState . flip runContT return

handleInput :: Event -> FlappyMonad ()
handleInput (EventKey (Char 'p') Down _ _) =
  gameState %= \case
    Running  -> Paused
    Paused   -> Running
    GameOver -> GameOver
handleInput (EventKey (SpecialKey key) Down _ _) | key `elem` jumpKeys = do
  velY .= jumpVel
  oldState <- gameState <<.= Running
  when (oldState == GameOver) $ do
    -- reset
    catPos.y .= 0
    catPos.x .= 0
    hurdles .= []
handleInput _ = return ()

step :: Float -> FlappyMonad ()
step dt = do
  state <- use gameState
  when (state /= Running) abort
  vy <- velY <+= dt*gravity
  py <- catPos.y <+= dt*vy
  when (py <= - h / 2) $ gameState .= GameOver
  d <- catPos.x <+= dt*velX
  hs <- hurdles <%= filter ((> (d-w)) . (^.hurdlePos.x))
  let lastX = fromMaybe (d+w) $ lastOf (traverse.hurdlePos.x) hs
  -- generate new hurdle
  when (lastX < d + 2*w) $ do
    hurdle <- lift $ zoom gen $ randomHurdle lastX
    hurdles .= hs ++ [hurdle]
  eps <- use $ to catExtremePoints
  unless (all id $ passes <$> eps <*> hs) $
    gameState .= GameOver
  where
    w = fromIntegral width
    h = fromIntegral height
