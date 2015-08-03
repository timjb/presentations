module Main where

import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Game
import Control.Lens
import Control.Monad.State.Lazy
import Paths_flappy_cat

import FlappyCat

-- Constants
jumpKeys :: [SpecialKey]
jumpKeys = [KeySpace, KeyEnter, KeyUp]

main :: IO ()
main = do
  socke      <- loadBMP =<< getDataFileName "socke-klein.bmp"
  background <- loadBMP =<< getDataFileName "socke-background.bmp"
  let renderHandler    = return . render socke background
      inputHandler evt = return . execState (handleInput evt)
      stepHandler dt   = return . execState (step dt)
  playIO displayMode white fps initialFlappyCat
    renderHandler inputHandler stepHandler
  where
    displayMode = InWindow "Flappy Cat" windowSize windowPos
    windowSize  = (width, height)
    windowPos   = (10, 10)
    fps = 30

render
  :: Picture -- ^ Socke
  -> Picture -- ^ Background
  -> FlappyCat
  -> Picture
render socke background fc
  | fc ^. gameOver =
      Translate (-170) (-20) $ Scale 0.5 0.5 $ Text "Game Over"
  | otherwise =
      let deg = atan (fc ^. velY / velX) * (-180/pi) in
      Pictures
      [ background
      , Translate (-170) (fc ^. posY) $ Rotate deg socke
      ]

handleInput :: Event -> State FlappyCat ()
handleInput (EventKey (SpecialKey key) state _ _) | key `elem` jumpKeys = do
  let pressedNow = state == Down
  wasPressed <- use pressed
  when (not wasPressed && pressedNow) $ do
    velY .= jumpVel
    isGameOver <- use gameOver
    when isGameOver $ do
      gameOver .= False
      posY .= 0
  pressed .= pressedNow
handleInput _ = return ()

step :: Float -> State FlappyCat ()
step dt = do
  vy <- velY <+= (dt * gravity)
  py <- posY <+= vy
  when (py <= bottom) $ gameOver .= True
  return ()
  where bottom = negate $ fromIntegral $ height `div` 2
