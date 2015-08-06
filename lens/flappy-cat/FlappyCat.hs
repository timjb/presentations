{-# LANGUAGE TemplateHaskell #-}

module FlappyCat where

import Control.Lens
import System.Random
import Graphics.Gloss.Interface.Pure.Game (KeyState (..), SpecialKey (..))
import Control.Monad.State.Lazy (MonadState (..))

-- Constants
jumpVel, gravity, velX :: Float
jumpVel = 250
gravity = -600
velX = 250
width, height :: Int
width  = 600
height = 400

jumpKeys :: [SpecialKey]
jumpKeys = [KeySpace, KeyEnter, KeyUp]

data Pos =
  Pos
  { _x :: Float
  , _y :: Float
  } deriving (Show, Eq)

makeLenses ''Pos

newtype Hurdle = Hurdle { _hurdlePos :: Pos } deriving (Show, Eq)

makeLenses ''Hurdle

randomHurdle :: (RandomGen g, MonadState g m) => Float -> m Hurdle
randomHurdle posX = state $ \g ->
  let (d, g')  = randomR (300, 600)  g
      (y, g'') = randomR (-130, 130) g'
  in (Hurdle (Pos (posX + d) y), g'')

passes :: Pos -> Hurdle -> Bool
passes pos hurdle =
  abs (pos^.x - hurdle^.hurdlePos.x) > 25 ||
  abs (pos^.y - hurdle^.hurdlePos.y) < 70

data GameState = Running | Paused | GameOver deriving (Eq, Show, Read)

data FlappyCat =
  FlappyCat
  { _gen :: StdGen
  , _gameState :: GameState
  , _catPos :: Pos
  , _velY :: Float
  , _hurdles :: [Hurdle]
  } deriving (Show)

makeLenses ''FlappyCat

initialFlappyCat :: FlappyCat
initialFlappyCat =
  FlappyCat
  { _gen = mkStdGen 42
  , _gameState = Running
  , _catPos = Pos 0 0
  , _velY = jumpVel
  , _hurdles = []
  }

catSlope :: FlappyCat -> Float
catSlope fc = - atan (fc^.velY / velX)

catExtremePoints :: FlappyCat -> [Pos]
catExtremePoints fc =
  map (translate . rotate . center . uncurry Pos)
    [(67,7), (71,26), (64,60), (51,63), (16,60), (1,1)]
  where
    center p = Pos (p^.x - 37) (32 - p^.y)
    rad = catSlope fc
    rotate p = Pos (  cos rad * p^.x + sin rad * p^.y)
                   (- sin rad * p^.x + cos rad * p^.y)
    translate p = Pos (p^.x + fc^.catPos.x) (p^.y + fc^.catPos.y)
