{-# LANGUAGE TemplateHaskell #-}

module FlappyCat where

import Control.Lens
import System.Random
import Control.Monad.State.Lazy (MonadState (..))

-- Constants
jumpVel, gravity, velX :: Float
jumpVel = 200
gravity = -450
velX = 150
width, height :: Int
width  = 600
height = 400

sockeExtremePoints :: [(Float, Float)]
sockeExtremePoints =
  map (\(x,y) -> (x - 37, 32 - y)) $
  [ (67,7)
  , (71,26)
  , (64,60)
  , (51,63)
  , (16,60)
  , (1,1)
  ]

data Hurdle =
  Hurdle
  { _hurdlePosX :: Float
  , _hurdleHeight :: Float
  }

makeLenses ''Hurdle

randomHurdle :: (RandomGen g, MonadState g m) => Float -> m Hurdle
randomHurdle posX = state $ \g ->
  let (dist, g')     = randomR (200, 600) g
      (hHeight, g'') = randomR (-140, 140) g'
  in (Hurdle (posX + dist) hHeight, g'')

passes :: (Float, Float) -> Hurdle -> Bool
passes (x, y) hurdle =
  abs (x - hurdle ^. hurdlePosX) > 25 ||
  abs (y - hurdle ^. hurdleHeight) < 70

data FlappyCat =
  FlappyCat
  { _gen :: StdGen
  , _pressed :: Bool
  , _gameOver :: Bool
  , _dist :: Float
  , _velY :: Float
  , _posY :: Float
  , _hurdles :: [Hurdle]
  }

makeLenses ''FlappyCat

initialFlappyCat :: FlappyCat
initialFlappyCat =
  FlappyCat
  { _gen = mkStdGen 42
  , _pressed = False
  , _gameOver = False
  , _dist = 0
  , _velY = jumpVel
  , _posY = 0
  , _hurdles = []
  }
