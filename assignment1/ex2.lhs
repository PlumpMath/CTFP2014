\documentclass{article}
\include{amsmath}
%include polycode.fmt

%format <> = "\oplus "

\begin{document}
Laws:

\begin{itemize}
\item $identity <> x = x$
\item $x <> identity = x$
\item $x <> (y <> z) = (x <> y) <> z$
\end{itemize}

> data Monoid a = Monoid
>   {  identity  :: a
>   ,  (<>)      :: a -> a -> a
>   }
>
> fold :: Monoid a -> [a] -> a
> fold  Monoid{..}  []        = identity
> fold  Monoid{..}  (x : xs)  = x <> fold Monoid{..} xs

$\mathbb{Z} \cup \{+\infty, -\infty\}$, useful so that min and max have
an identity.

> data Number
>   =  Top
>   |  Bot
>   |  Z Integer
>   deriving (Eq, Ord, Show, Read)
>
> instance Num Number where
>   fromInteger = Z
>
>   negate (Z n) = Z (-n)
>   negate _     = error "Number: Can't negate infinities"
>
> _Min :: Monoid Number
> _Min = Monoid
>   {  identity = Top
>   ,  (<>) = \x0 y0 -> case (x0, y0) of
>        (Top, x)    -> x
>        (x,   Top)  -> x
>        (Bot, _)    -> Bot
>        (_,   Bot)  -> Bot
>        (Z x, Z y)  -> Z (min x y)
>   }
>
> _Max :: Monoid Number
> _Max = Monoid
>   {  identity = Bot
>   ,  (<>) = \x0 y0 -> case (x0, y0) of
>        (Bot, x)    -> x
>        (x,   Bot)  -> x
>        (Top, _)    -> Top
>        (_,   Top)  -> Top
>        (Z x, Z y)  -> Z (max x y)
>   }

Lemmas

> minimax :: [[Number]] -> Number

< minimax = fold _Min . map (fold _Max)

> minimax = foldl help1 Top

> help1 :: Number -> [Number] -> Number

< help1 a xs = a `min` fold _Max xs
< help1 a xs = fold _Max (map (min a) xs)

> help1 a xs = foldl (help2 a) Bot xs

> help2 :: Number -> Number -> Number -> Number
> help2 a b c = b `max` (a `min` c)

\end{document}
