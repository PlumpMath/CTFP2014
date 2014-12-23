%if false

> {-# LANGUAGE RecordWildCards #-}

%endif

\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\theoremstyle{plain}

%include polycode.fmt

%format <> = "\oplus "
%format x_0 = "x_0 "
%format y_0 = "y_0 "

\newtheorem*{lemma*}{Lemma}

\begin{document}

In this example, we're going to optimize the ``minimax'' algorithm
using equational reasoning and the laws of |map| and |fold|.

\section{Prerequisites}

\subsection{|fold|s and |Number|s}

To specify and use an Haskell version of the |/| ``reduce'' operator,
we define a record characterizing monoids.  We do this since following
the presentation in the paper we want to perform reductions without
specifying the identity element each time, and relying on the
associativity of our binary operator.

> data Monoid a = Monoid
>   {  identity  :: a
>   ,  (<>)      :: a -> a -> a
>   }

The laws for |Monoid|:

\begin{itemize}
\item |identity <> x = x| (left identity)
\item |x <> identity = x| (right identity)
\item |x <> (y <> z) = (x <> y) <> z| (associativity)
\end{itemize}

We choose not to use the existing |Monoid| typeclass since to be able
to provide different |Monoid|s over the same type to our reducing
function, |fold|:

> fold :: Monoid a -> [a] -> a
> fold  Monoid{..}  []        = identity
> fold  Monoid{..}  (x : xs)  = x <> fold Monoid{..} xs

Moreover, to specify the |minimax| function, we need a type that forms
a |Monoid| with the |max| and |min| operators.  |Integer| will not work,
since it has no identity element for |min| and |max|.  We fix that by
defining:

> data Number
>   =  Bot
>   |  Z Integer
>   |  Top

%if false

>   deriving (Eq, Ord, Show, Read)

%endif

Where |Bot| represents $-\infty$, and |Top| $+\infty$.

We also define an incomplete |Num| instance for |Number|, so that we
can use integer literals:

> instance Num Number where
>   fromInteger = Z
>
>   negate (Z n) = Z (-n)
>   negate (Top) = Bot
>   negate (Bot) = Top

Finally, we can define the |Monoid|s that we are interested in:

> _Min :: Monoid Number
> _Min = Monoid
>   {  identity = Top
>   ,  (<>) = \x_0 y_0 -> case (x_0, y_0) of
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
>   ,  (<>) = \x_0 y_0 -> case (x_0, y_0) of
>        (Bot, x)    -> x
>        (x,   Bot)  -> x
>        (Top, _)    -> Top
>        (_,   Top)  -> Top
>        (Z x, Z y)  -> Z (max x y)
>   }

\subsection{Useful lemmas}

The last ingredient before starting to work on the minimax algorithm
is some useful lemmas regarding |map| and |fold|.

\begin{lemma*}
\emph{(|map| distributivity)}
\label{distributivity}

|map| distributes (backwards) through functional composition:

< map (f . g) = map f . map g

\end{lemma*}

\begin{lemma*}
\emph{(specialization)}
\label{specialization}

Every homomorphism on lists can be expressed as a left (or also a
right) reduction.  More precisely,

< fold m . map f = foldl (\a b -> a <> f b) identity

Where |m| is some |Monoid| with identity |identity| and binary
operator |<>|.

\end{lemma*}

\section{Minimax}

Given a list of numbers, we want an efficient algorithm that computes
the minimum of the maximum numbers in each list.

Our starting function is an obvious implementation of the
specification above:

> minimax :: [[Number]] -> Number
> minimax = fold _Min . map (fold _Max)

Using the specialization lemma, we can write

< minimax = foldl help1 Top

where

> help1 :: Number -> [Number] -> Number
> help1 a xs = a `min` fold _Max xs

Since |min| distributes through |max| we have

< help1 a = fold _Max . map (min a)

Using the specialization lemma a second time, we have

< help1 a = foldl (\b c -> b `max` (a `min` c)) Bot

\section{The alpha-beta algorithm}

We now generalise the minimax problem to trees. Consider the data-type

> data Tree = Tip Number | Fork [Tree]

We wish to calculate an efficient algorithm for computing a function
|eval| as follows:

%if False

> neg :: Num a => a -> a
> neg = negate

%endif

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
<         =  help2 Bot Top t

We have, without iventiveness, reduced the problem of calculating
|eval t| to that of evaluting |help2 a b t| for values of |a| and |b|.

Let us now expand the definition of |help2 a b t| in a similar way as
we did for |help1 a t|. We obtain

< help2 a b (Tip n)    =  b `min` (a `max` n)
< help2 a b (Fork ts)  =  b `min` (a `max` (fold _Max (map (neg . eval) ts)))

In order to simplify the right-hand side of this last equation, we need
the dual-distributive law

< b `min` (a `max` c) = (b `min` a)  `max` (b `min` c)

and the fact that evaluation of |help2 a b t| is required only for
values of |a| and |b| satisfying |a == a `min` b|, in other words,
for |a <= b|.  In such case we have

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
