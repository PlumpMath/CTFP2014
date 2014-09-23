\documentclass{article}
\include{amsmath}
%include polycode.fmt
\begin{document}
\begin{code}
import Prelude hiding (min, max)
import qualified Prelude

import Common

\end{code}
$\mathbb{Z} \cup \{+\infty, -\infty\}$, useful so that min and max have an identity.
\begin{code}
data Number
  =  Top
  |  Bot
  |  Z Integer
  deriving (Eq, Ord, Show, Read)

instance Num Number where
  fromInteger = Z

  negate (Z n) = Z (-n)
  negate _     = error "Number: Can't negate infinities"

min :: Monoid Number
min = Monoid
  {  identity = Top
  ,  (<>) = \x0 y0 -> case (x0, y0) of
       (Top, x)    -> x
       (x,   Top)  -> x
       (Bot, _)    -> Bot
       (_,   Bot)  -> Bot
       (Z x, Z y)  -> Z (Prelude.min x y)
  }

max :: Monoid Number
max = Monoid
  {  identity = Bot
  ,  (<>) = \x0 y0 -> case (x0, y0) of
       (Bot, x)    -> x
       (x,   Bot)  -> x
       (Top, _)    -> Top
       (_,   Top)  -> Top
       (Z x, Z y)  -> Z (Prelude.max x y)
  }

minimax :: [[Number]] -> Number
minimax = fold min . map (fold max)
\end{code}
\end{document}
