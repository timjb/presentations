module Main where

import Graphics.Gloss
import Graphics.Gloss.Interface.IO.Game
import Control.Lens
import Control.Monad.State.Lazy
import Data.Maybe (fromMaybe)
import Paths_flappy_cat

import FlappyCat

-- Constants
jumpKeys :: [SpecialKey]
jumpKeys = [KeySpace, KeyEnter, KeyUp]

main :: IO ()
main = do
  socke      <- loadBMP =<< getDataFileName "socke-klein.bmp"
  background <- loadBMP =<< getDataFileName "socke-background.bmp"
  wfda       <- loadBMP =<< getDataFileName "was-ficht-dich-an.bmp"
  let renderHandler    = return . render socke background wfda
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
  -> Picture -- ^ Schnurrli, was ficht dich an?
  -> FlappyCat
  -> Picture
render socke background wfda fc
  | fc ^. gameOver =
      Pictures
      [ Translate (-110) (-150) $ Scale 0.3 0.3 $ Text "Game Over"
      , Translate 0 20 $ wfda
      ]
  | otherwise =
      let deg = atan (fc ^. velY / velX) * (-180/pi) in
      Pictures
      [ background
      , Translate (-200) 0 $ Color (dim orange) $
          Pictures $ fc ^.. hurdles.traverse.to renderHurdle
      , Translate (-200) (fc ^. posY) $ Rotate deg socke
      , Color white $ Translate (-290) 170 $ Scale 0.15 0.15 $
          Text $ show $ round $ fc ^. dist
      ]
  where
    renderHurdle hurdle =
      let x = (hurdle ^. hurdlePosX) - (fc ^. dist)
          rectPath y1 y2 = [(x-25,y1), (x+25,y1), (x+25,y2), (x-25,y2)]
          hh = hurdle ^. hurdleHeight
      in Pictures
         [ Polygon $ rectPath (-200) (hh - 70)
         , Polygon $ rectPath (hh + 70) 200
         ]

handleInput :: Event -> State FlappyCat ()
handleInput (EventKey (SpecialKey key) state _ _) | key `elem` jumpKeys = do
  let pressedNow = state == Down
  wasPressed <- use pressed
  when (not wasPressed && pressedNow) $ do
    velY .= jumpVel
    isGameOver <- use gameOver
    when isGameOver $ do
      -- Reset
      gameOver .= False
      posY .= 0
      dist .= 0
      hurdles .= []
  pressed .= pressedNow
handleInput _ = return ()

step :: Float -> State FlappyCat ()
step dt = do
  vy <- velY <+= (dt * gravity)
  py <- posY <+= (dt * vy)
  when (py <= bottom) $ gameOver .= True
  d <- dist <+= dt * velX
  hs <- hurdles <%= filter ((> (d - 400)) . (^. hurdlePosX))
  let lastX = fromMaybe (d+600) $ lastOf (traverse.hurdlePosX) hs
  when (lastX < d+800) $ do
    hurdle <- zoom gen $ randomHurdle lastX
    hurdles .= hs ++ [hurdle]
  let rad = atan (vy / velX)
      criticalPoints =
        flip map sockeExtremePoints $ \(x, y) ->
          (d + cos rad * x + sin rad * y, py - sin rad * x + cos rad * y)
  return ()
  unless (all (uncurry passes) $ (,) <$> criticalPoints <*> hs) $ do
    gameOver .= True
  where bottom = negate $ fromIntegral $ height `div` 2
