\documentclass{article}
\include{amsmath}
%include polycode.fmt

%format <> = "\oplus "

\begin{document}
Laws:

\begin{itemize}
\item |identity <> x = x|
\item |x <> identity = x|
\item |x <> (y <> z) = (x <> y) <> z|
\end{itemize}

> data Monoid a = Monoid
>   {  identity  :: a
>   ,  (<>)      :: a -> a -> a
>   }

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

%if False

Here just so we can use literals...

> instance Num Number where
>   fromInteger = Z
>
>   negate (Z n) = Z (-n)
>   negate _     = error "Number: Can't negate infinities"

%endif

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


> minimax :: [[Number]] -> Number
> minimax = fold _Min . map (fold _Max)

< minimax = foldl help1 Top

> help :: Number -> [Number] -> Number
> help a xs = a `min` fold _Max xs

< help a xs = fold _Max (map (min a) xs)
< help a xs = foldl (\b c -> b `max` (a `min` c)) Bot xs

\section{The alpha-beta algorithm}

We now generalise the minimax problem to trees. Consider the data-type

> data Tree = Tip Number | Fork [Tree]

We wish to calculate an efficient algorithm for computing a function
|eval| as follows:

< eval :: Tree -> Number
< eval (Tip n)    =  n
< eval (Fork ts)  =  fold _Max (map (neg . eval) ts)

Where |neg| is a shorthand for |negate|.

Using the specialisation lemma on the right-hand side of the second
equation for |eval|, we obtain

< eval (Fork ts)  =  foldl help1 Bot ts

where

< help1 :: Number -> Tree -> Number
< help1 a t  =  a `max` neg (eval t)

We now expand this last equation by considering the two possible forms
for a tree |t|:

< help1 a (Tip n)    =  a `max` neg n
< help1 a (Fork ts)  =  a `max` neg (fold _Max (map (neg . eval) ts))

The last equation can now be simplified using the laws

< neg (a `max` b)    =  neg a `min` neg b
< a `max` (b `min`c)  =  (a `max` b) `min` (a `max` c)

We obtain

< help1 a (Fork ts)  = fold _Min (map (max a) (map eval ts))

After using the |map| distributivity law, the right-hand side of this
equation is also a candidate for specialisation. We have

< help1 a (Fork ts)  = foldl (help2 a) Top ts

where

< help2 :: Number -> Number -> Tree -> Number
< help2 a b t  =  b `min` (a `max` eval t)

Furthermore, since

< eval t  =  Top `min` (Bot `max` eval t)
<         =  Top (help2 Bot) t

We have, without iventiveness, reduced the problem of calculating |eval
t| to that of evaluationg |help2 a b t| for values of |a| and
|b|.

Let us now expand the definition of |help2 a b t| in a similar way as
we did for |help1 a t|. We obtain

< help2 a b (Tip n)    =  b `min` (a `max` n)
< help2 a b (Fork ts)  =  b `min` (a `max` (fold _Max (map (neg . eval) ts)))

In order to simplify the right-hand side of this last equation, we need
the dual-distributive law

< b `min` (a `max` c) = (b `min` a)  `max` (b `min` c)

and the fact that evaluation of |help2 a b t| is required only for
values of |a| and |b| satisfying |a = a `min` b|, in other words,
for $a \leq b$.  In such case we have

< b `min` (a `max` c) = a  `max` (b `min` c)

by commutativity of |min|.
We then obtain

< help2 a b (Fork ts)  =
<   a `max` (fold _Max (map (min b) (map (neg . eval) ts)))

Using specialisation yet a third time, we obtain

< help2 a b (Fork ts) = foldl (help3 b) a ts

where

< help3 :: Number -> Number -> Tree -> Number
< help3 b a t  =  a `max` (b `min` (neg . eval) t)

At this point, the seemingly endless succession of expansion and
specialisation steps can be stopped.  A short calculation using the
given properties of |-|, |min| and |max| yields

< help3 b a t  =  neg (help2 (neg b) (neg a) t)

Putting everything together, we now have

> eval :: Tree -> Number
> eval t =  help2 Bot Top t
>
> help2 :: Number -> Number -> Tree -> Number
> help2 a b (Tip n)    =  b `min` (a `max` n)
> help2 a b (Fork ts)  =  foldl (help3 b) a ts
>
> help3 :: Number -> Number -> Tree -> Number
> help3 b a t =  neg (help2 (neg b) (neg a) t)

Finally, we bring on the left-zeros (absorbing elements).  We only need
to observe that |b| is a left-zero of |help3 b|.  This follows from
the definition of |help3 b| and the absorbtive law

< b `max` (b `min` x) = b

Incorporating this optimisation yields the alpha-beta algorithm.

The various axioms concerning |max|, |min|, |-|, |Top| and
|Bot| used in the above derivation are precisely those of a boolean
algebra.

\end{document}
