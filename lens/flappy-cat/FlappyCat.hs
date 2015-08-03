{-# LANGUAGE TemplateHaskell #-}

module FlappyCat where

import Control.Lens

-- Constants
jumpVel, gravity, velX :: Float
jumpVel = 12
gravity = -30
velX = 10
width, height :: Int
width  = 600
height = 400

data FlappyCat =
  FlappyCat
  { _pressed :: Bool
  , _gameOver :: Bool
  , _velY :: Float
  , _posY :: Float
  }

makeLenses ''FlappyCat

initialFlappyCat :: FlappyCat
initialFlappyCat =
  FlappyCat
  { _pressed = False
  , _gameOver = False
  , _velY = jumpVel
  , _posY = 0
  }
