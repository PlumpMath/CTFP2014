\documentclass{article}
%include polycode.fmt
%format ostar = "\oast "
%format oplus = "\oplus "
%format * = "\cdot "
%format theta = "\theta"

\usepackage{amsthm}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}{Corollary}

\begin{document}
\section{Max Rectangle}

\textit{By Daniel O, Irene, Pablo, Fabian and Jeremy.}

> module MaxRectangle where

> import qualified Prelude
> import Prelude hiding (Left, map)

> class Binoid a where
>   (+^) :: a -> a -> a
>   (*^) :: a -> a -> a

Satifsies
< (a +^ b) +^ c == a +^ (b +^ c)
< (a *^ b) *^ c == a *^ (b *^ c)

Satisfies
< (a +^ b) *^ (c +^ d) == (a *^ c) +^ (b *^ d)

> left, right :: a -> a -> a
> left  a _ = a
> right _ b = b

> newtype Left a = Left { mkLeft :: a }

> instance Binoid (Left a) where
>   (+^) = left
>   (*^) = left

> dot :: Eq a => a -> a -> a
> dot a b | a == b    = a
>         | otherwise = undefined

> data Array a
>   = Singleton a
>   | Above (Array a) (Array a)
>   | Beside (Array a ) (Array a)
>   deriving Show

> (|||) :: Array a -> Array a -> Array a
> (|||) = Beside

> (|-|) :: Array a -> Array a -> Array a
> (|-|) = Above

> lift :: a -> Array a
> lift a = Singleton a

> height :: Array a -> Int
> height (Singleton _) = 1
> height (Above x y)   = height x + height y
> height (Beside x y)  = height x `dot` height y

> width :: Array a -> Int
> width (Singleton _) = 1
> width (Above x y)   = width x `dot` width y
> width (Beside x y)  = width x + width y

> ex :: Array Int
> ex = (lift 1 |-| lift 3) ||| (lift 2 |-| lift 4) ||| (lift 5 |-| lift 6)

> map :: (a -> b) -> Array a -> Array b
> map f (Singleton a) = Singleton $ f a
> map f (Above x y)   = map f x `Above` map f y
> map f (Beside x y)  = map f x `Beside` map f y

> reduce :: (a -> a -> a) -> (a -> a -> a) -> Array a -> a
> reduce f g (Singleton a) = a
> reduce f g (Above x y)   = reduce f g x `f` reduce f g y
> reduce f g (Beside x y)  = reduce f g x `g` reduce f g y

> -- See lecture notes 1.9 Segments
> segs :: Array a -> [Array a]
> segs = undefined

> -- See lecture notes 4.6 Zip
> -- NB: I think it might be Array (Array) whilst listrows and listcols do produce lists
> rows :: Array a -> [Array a]
> rows = undefined

> cols :: Array a -> Array (Array a)
> cols = undefined

> listrows :: Array a -> [[a]]
> listrows = undefined

> listcols :: Array a -> [[a]]
> listcols = undefined


> -- See lecture notes 4.7 Directed reductions (⤈)   TODO: name changes where appropriate
>
> singleExtract :: Array a -> a
> singleExtract (Singleton x) = x

> columnReduce :: (a -> a -> a) -> Array a -> Array a
> columnReduce f (Singleton z)             = Singleton z
> columnReduce f (Above x (Singleton y))   = Singleton $ singleExtract (columnReduce f x) `f` y
> columnReduce f (Beside x y)              = Beside    (columnReduce f x) (columnReduce f y)

> rowReduce :: (a -> a -> a) -> Array a -> Array a
> rowReduce f (Singleton z)            = Singleton z
> rowReduce f (Beside x (Singleton y)) = Singleton $ singleExtract (rowReduce f x) `f` y
> rowReduce f (Above x y)              = Above (rowReduce f x) (rowReduce f y)

Satisfy
< rows == rowReduce Beside . map Singleton
< cols == columnReduce Above . map Singleton


> -- See lecture notes 4.8 Accumulations (⇟)    TODO: name changes where appropriate

Considering the array element selectors/extractors

> bottomleft :: Array a -> a
> bottomleft = reduce right left

> topright :: Array a -> a
> topright = reduce left right

We define

> accumulateCols :: (a -> a -> a) -> Array a -> Array a
> accumulateCols f (Singleton z) = Singleton z
> accumulateCols f (Above x (Singleton y)) = Above xs (Singleton (f (bottomleft xs) y))
>   where xs = accumulateCols f x
> accumulateCols f (Beside x y) = Beside (accumulateCols f x) (accumulateCols f y)

> accumulateRows :: (a -> a -> a) -> Array a -> Array a
> accumulateRows f (Singleton z) = Singleton z
> accumulateRows f (Beside x (Singleton y)) = Beside xs (Singleton (f (topright xs) y))
>   where xs = accumulateRows f x
> accumulateRows f (Above x y) = Beside (accumulateRows f x) (accumulateRows f y)

Satisfying
< listrows . (accumulateRows f) == map (scanl f) . listrows
< listcols . (accumulateCols f) == map (scanl f) . listcols


> -- See lecture notes 4.9 Tops and bottoms

In a similar fashion to tails and inits

> lefts :: Array a -> Array (Array a)
> lefts = accumulateRows Beside . cols

> tops :: Array a -> Array (Array a)
> tops = accumulateCols Above . rows

\begin{lemma}[Accumulation lemma]

< map (columnReduce f) . tops  = rows . accumulateCols f

< map (rowReduce f)    . lefts = cols . accumulateRows f

\end{lemma}

\begin{proof}
Given the orthogonal reduction rules
< map (columnReduce f) . lefts = lefts . columnReduce f
< map (rowReduce f)    . tops  = tops  . rowReduce f

and the orthogonal accumulation rules
< map (accumulateCols f) . lefts = lefts . accumulateCols f
< map (accumulateRows f) . tops  = tops  . accumulateRows f

We obtain
\begin{spec}
missing
\end{spec}

\end{proof}


> -- See lecture notes 4.11 Rectangles
> vsegs :: Array a -> [Array a]
> vsegs = undefined

> -- See lecture notes 4.11 Rectangles
> rects :: Array a -> [Array a]
> rects = undefined

> -- See lecture notes 4.14 Application
> area :: Array a -> Int
> area = reduce (+) (+) . map (const 1)

> -- See lecture notes 4.14 Application
> filled :: Array Int -> Bool
> filled = reduce (&&) (&&) . map (== 1)

> -- See lecture notes 4.14 Application (R)
> r, r' :: Array Int -> Int
> r  = foldl max 0 . Prelude.map area . filter filled . rects
> r' = foldl max 0 . Prelude.map h . rows . accumulateCols ostar
>   where
>     h = foldl max 0 . Prelude.map f . segs
>     f x = width x * reduce min min x

>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b

>     ostar :: Int -> Int -> Int
>     ostar a b = max (a `oplus` b) b

\begin{lemma}[BRTL rule]
\label{lem:brtl}
We will prove that

< reduce Above Beside . map vsegs . bottoms =
<    reduce Above Beside . map bottoms . vsegs

\begin{proof}

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

We introduce the abbreviations |theta = reduce Above Beside|, |V = vsegs| and |B = bottoms|.
We observe that |theta . map B . lefts = theta . map lefts . B| and
|theta . map B . rights = theta . map rights . B|.

Now we argue:

\begin{spec}
  theta . map V . B
= {- definition of |vsegs| -}
  theta . map (theta . map rights . lefts) . B
= {- map distributivity -}
  theta . map theta . map (map rights) . map lefts . B
= {- reduce/reduce promotion -}
  theta . theta . map (map rights) . map lefts . B
= {- map and reduce promotion -}
  theta . map rights . theta . map lefts . B
= {- observation -}
  theta . map rights . theta . map B . lefts
= {- map and reduce promotion -}
  theta . theta . map (map rights) . map B . lefts
= {- reduce/reduce promotion -}
  theta . map theta . map (map rights) . map B . lefts
= {- map distributivity -}
  theta . map (theta . map rights . B) . lefts
= {- observation -}
  theta . map (theta . map B . rights) . lefts
= {- map distributivity -}
  theta . map theta . map (map B) . map rights . lefts
= {- reduce/reduce promotion -}
  theta . theta . map (map B) . map rights . lefts
= {- map and reduce promotion -}
  theta . map B . theta . map rights . lefts
= {- definition of |vsegs| -}
  theta . map B . vsegs
\end{spec}

\end{proof}

\end{lemma}

\begin{lemma}[Rectangle decomposition]
\label{lem:rectangle-decomposition}
If for some |g|, |ostar|

< reduce (oplus) (oplus) . map f . bottoms = g . columnReduce (ostar)

then

< reduce (oplus) (oplus) . map f . rects =
<    reduce (oplus) (oplus) . map h . rows . accumulateCols (ostar)
<   where
<     h = reduce (oplus) (oplus) . map g . vsegs
\end{lemma}

\begin{proof}

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

We shall need the following observation about |rects|:
\begin{spec}
  rects
= {- one definition of |rects| -}
  reduce Above Beside . map vsegs .  hsegs
= {- definition of |hsegs| -}
  reduce Above Beside . map vsegs . reduce Above Beside . map bottoms . tops
= {- map and reduce promotion -}
  reduce Above Beside . map (reduce Above Beside . map vsegs . bottoms) . tops
= {- BRTL rule (Lemma~\ref{lem:brtl}) -}
  reduce Above Beside . map (reduce Above Beside . map bottoms . vsegs) . tops
\end{spec}

Now we argue:
\begin{spec}
  reduce (oplus) (oplus) . map f . rects
= {- previous observation -}
  reduce (oplus) (oplus) . map f .  reduce Above Beside
      . map (reduce Above Beside . map bottoms . vsegs) . tops
= {- map and reduce promotion -}
  reduce (oplus) (oplus)
      . map  (reduce (oplus) (oplus) . map f
             . reduce Above Beside . map bottoms . vsegs)
      . tops
= {- promotion rules -}
  reduce (oplus) (oplus)
      . map  (reduce (oplus) (oplus)
             . map (reduce (oplus) (oplus) . map f . bottoms)
             . vsegs)
      . tops
= {- assumption -}
  reduce (oplus) (oplus)
      . map (reduce (oplus) (oplus) . map (g . columnReduce (ostar)) . vsegs)
      . tops
= {- map distributivity -}
  reduce (oplus) (oplus)
      . map (reduce (oplus) (oplus) . map g . map (columnReduce (ostar)) . vsegs)
      . tops
= {- orthogonal reduction rule -}
  reduce (oplus) (oplus)
      . map (reduce (oplus) (oplus) . map g . vsegs . columnReduce (ostar))
      . tops
= {- map distributivity; |h = reduce oplus oplus . map g . vsegs| -}
  reduce (oplus) (oplus) . map h . map (columnReduce (ostar)) . tops
= {- accumulation lemma -}
  reduce (oplus) (oplus) . map h . rows . accumulateCols (ostar)
\end{spec}


\end{proof}


\begin{lemma}\hfill
< reduce max max . map (reduce oplus oplus) . bottoms

can be expressed as

< (\ x -> width x * foldl min undefined x) . columnReduce ostar
\end{lemma}

\begin{proof}
missing
\end{proof}


\begin{corollary}\hfill
< reduce max max . map (reduce oplus oplus) . rects

can be expressed as

< reduce max max . map (reduce max max . map g . vsegs) . rows . accumulateCols ostar
\end{corollary}

\begin{proof}
Apply Lemma 1 to Lemma 2.
\end{proof}


\begin{lemma}[Filter erasure]\hfill
< reduce oplus oplus x = if filled x then area x else 0
<   where
<     oplus 0 _ = 0
<     oplus _ 0 = 0
<     oplus a b = a + b
\end{lemma}

\begin{proof}
missing
\end{proof}


\begin{theorem}\hfill
< foldl max 0 . map area . filter filled . rects

can be expressed as

< fold max . map (foldl max 0 . map (\ x -> length x * foldl min undefined x) . segs) . rows . accumulateCols ostar
\end{theorem}

\begin{proof}\hfill
< foldl max 0 . map area . filter filled . rects

= Filter erasure (OBS: the result for empty arrays is zero, was -∞ before)

< reduce max max . map (reduce oplus oplus) . rects

= Rectangle decomposition

< foldl max 0 . map (foldl max 0 . map (\ x -> width x * foldl min undefined x) . vsegs) . rows . accumulateCols ostar

= On lists

< foldl max 0 . map (foldl max 0 . map (\ x -> length x * foldl min undefined x) . segs) . rows . accumulateCols ostar
\end{proof}


\begin{corollary}
The largest filled rectangle can be computed in linear time.
\end{corollary}

\begin{proof}
missing
\end{proof}
\end{document}
