\documentclass{article}
%include polycode.fmt
%format ostar = "\oast "
%format oplus = "\oplus "
%format otimes = "\otimes "
%format odot = "\odot "
%format * = "\cdot "
%format theta = "\theta"

\usepackage{amsmath}
\usepackage{amsthm}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}{Corollary}

\begin{document}
\section{Max Rectangle}

\textit{By Daniel O, Irene, Pablo, Fabian and Jeremy.}

> module MaxRectangle where

> import qualified Prelude
> import Prelude hiding (Left, map, zipWith)



> class Binoid a where
>   (+^) :: a -> a -> a
>   (*^) :: a -> a -> a

Satifsies
< (a +^ b) +^ c == a +^ (b +^ c)
< (a *^ b) *^ c == a *^ (b *^ c)

Satisfies
< (a +^ b) *^ (c +^ d) == (a *^ c) +^ (b *^ d)

> oplus :: a -> a -> a
> oplus = undefined
> otimes :: a -> a -> a
> otimes = undefined

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

so that (map distributivity)

< map (f . g) = map f . map g

> reduce :: (a -> a -> a) -> (a -> a -> a) -> Array a -> a
> reduce f g (Singleton a) = a
> reduce f g (Above x y)   = reduce f g x `f` reduce f g y
> reduce f g (Beside x y)  = reduce f g x `g` reduce f g y

so that (join rules)

< map f . reduce (|-|) (|||) = reduce (|-|) (|||) . map (map f)
< reduce oplus otimes reduce (|-|) (|||) = reduce oplus otimes . map (reduce oplus otimes)

> zipWith :: (a -> a -> a) -> Array a -> Array a -> Array a
> zipWith op (Singleton a) (Singleton b)  = Singleton $ a `op` b
> zipWith op (Above x y)   (Above x' y')  = zipWith op x y `Above`  zipWith op x' y'
> zipWith op (Beside x y)  (Beside x' y') = zipWith op x y `Beside` zipWith op x' y'

> -- See lecture notes 1.9 Segments
> segs :: Array a -> [Array a]
> segs = undefined

> -- See lecture notes 4.6 Zip
> rows :: Array a -> Array (Array a)
> rows = reduce (|-|) (zipWith (|||)) . map (lift . lift)

> cols :: Array a -> Array (Array a)
> cols = reduce (zipWith (|-|)) (|||) . map (lift . lift)

> listrows :: Array a -> [[a]]
> listrows = reduce (++) (Prelude.zipWith (++)) . map (\ x -> [[x]])

> listcols :: Array a -> [[a]]
> listcols = reduce (Prelude.zipWith (++)) (++) . map (\ x -> [[x]])

so that

< height = length . listrows
< width = length . listcols

and

< listcols = listrows . tr
< listrows = listcols . tr

as well as

< reduce oplus otimes = fold oplus . map (fold otimes) . listrows
< reduce oplus otimes = fold otimes . map (fold oplus) . listcols


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

> rights :: Array a -> Array (Array a)
> rights = undefined

> bottoms :: Array a -> Array (Array a)
> bottoms = undefined

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



\begin{lemma}[Horner's rule]
\label{lem:horner}
Analogue of Horner's rule for arrays:

< reduce oplus oplus . map (reduce otimes odot) . bottoms

OBS: corrected a probable mistake in the paper.

It is necessary that otimes distributes over oplus and oplus abides with odot.
These properties allow one to prove that:

< reduce oplus oplus . map (reduce otimes odot) . bottoms = reduce odot odot .  rowReduce ostar

Where ostar is defined as:

> ostar :: a -> a -> a
> a `ostar` b = (a `otimes` b) `oplus` b

\end{lemma}

\begin{proof}
missing
\end{proof}

An example case:

\begin{equation*}
x = \begin{pmatrix}
    1 & 2 \\
    3 & 4 \\
    5 & 6 \\
\end{pmatrix}
\end{equation*}

LHS:

< ((1 `otimes` 3 `otimes` 5) `odot` (2 `otimes` 4 `otimes` 6)) `oplus` ((3 `otimes` 5) `odot` (4 `otimes` 6)) `oplus` (5 `odot` 6)

oplus and odot abide:

< ((1 `otimes` 3 `otimes` 5) `oplus` (3 `otimes` 5) `oplus` 5) `odot` ((2 `otimes` 4 `otimes` 6) `oplus` (4 `otimes` 6) `oplus` 6)

distribution of otimes over oplus:

< ((((1 `otimes` 3) `oplus` 3) `otimes` 5) `oplus` 5) `odot` ((((2 `otimes` 4) `oplus` 4) `otimes` 6) `oplus` 6)

use ostar to simplify:

< ((1 `ostar` 3) `ostar` 5) `odot` ((2 `ostar` 4) `ostar` 6)

and finally:

< reduce odot odot (rowReduce ostar x)

which is the RHS.




4.11 Rectangles

Top-lefts of an array.  Analogous to ``inits'' for lists.

> topls :: Array a -> Array (Array a)
> topls = reduce (|-|) (|||) . map tops . lefts

Example:

\[
topls \begin{pmatrix}
1 & 2 & 3 \\
4 & 5 & 6 \\
7 & 8 & 9 \\
\end{pmatrix} = \begin{pmatrix}
\begin{pmatrix} 1\\\end{pmatrix} & \begin{pmatrix}1&2\\\end{pmatrix} & \begin{pmatrix}1&2&3\\\end{pmatrix} \\
\begin{pmatrix} 1\\4\\\end{pmatrix} & \begin{pmatrix}1&2\\4&5\\\end{pmatrix} & \begin{pmatrix}1&2&3\\4&5&6\\\end{pmatrix} \\
\begin{pmatrix} 1\\4\\7\\\end{pmatrix} & \begin{pmatrix}1&2\\4&5\\7&8\\\end{pmatrix} & \begin{pmatrix}1&2&3\\4&5&6\\7&8&9\\\end{pmatrix} \\
\end{pmatrix}
\]

Bottom rights, like ``tails''.

> botrs :: Array a -> Array (Array a)
> botrs = reduce (|-|) (|||) . map bottoms . rights

Horizontal segments:

> hsegs :: Array a -> Array (Array a)
> hsegs = reduce (|-|) (|||) . map bottoms . tops

Vertical segments:

> vsegs :: Array a -> Array (Array a)
> vsegs = reduce (|-|) (|||) . map rights . lefts

One way of defining the rectangles:

> rects :: Array a -> Array (Array a)

< rects = reduce (|-|) (|||) . map botrs . topls

Another way:

> rects = reduce (|-|) (|||) . map hsegs . vsegs




> -- See lecture notes 4.14 Application
> area :: Array a -> Int
> area = reduce (+) (+) . map (const 1)

> -- See lecture notes 4.14 Application
> filled :: Array Int -> Bool
> filled = reduce (&&) (&&) . map (== 1)

> -- See lecture notes 4.14 Application (R)
> r, r' :: Array Int -> Int
> r  = foldl max 0 . Prelude.map area . filter filled . bag . rects
>   where
>     bag = reduce (++) (++) . map (\ x -> [x])
> r' = reduce max max . map h . rows . accumulateCols ostar
>   where
>     h = foldl max 0 . Prelude.map f . segs
>     f x = width x * reduce min min x
>
>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b
>
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
= {- join rules and map distributivity -}
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


\begin{lemma}\label{lem:a}
If solely arrays over $\{0, 1\}$ are considered, then

< reduce max max . map (reduce oplus oplus) . bottoms
<   where
<     oplus 0 _ = 0
<     oplus _ 0 = 0
<     oplus a b = a + b

can be expressed as

< (\ x -> width x * reduce min min x) . columnReduce ostar
<   where
<     ostar _ 0 = 0
<     ostar a b = a + b
\end{lemma}

\begin{proof}\hfill
< reduce max max . map (reduce oplus oplus) . bottoms

= $x \in \{ 0, 1 \}^{n \times m}$: |reduce oplus oplus x = width x * reduce oplus min x|

< reduce max max . map (\ y -> width y * reduce oplus min y) . bottoms

= all bottoms have the same width

< reduce max max $ map (\ y -> width x . reduce oplus min y) $ bottoms x

= map distributivity

< reduce max max $ map (width x *) $ map (reduce oplus min) $ bottoms x

= the width is a positive number

< width x * (reduce max max . map (reduce oplus min) . bottoms) x

= Horner's rule: |oplus| distributes through |max|, and |min| abides with |oplus|

< width x * (reduce min min . columnReduce ostar) x

= |columnReduce| preserves the width

< (\ x -> width x * reduce min min x) . columnReduce ostar
\end{proof}


\begin{corollary}\hfill
< reduce max max . map (reduce oplus oplus) . rects

can be expressed as

< reduce max max . map (reduce max max . map g . vsegs) . rows . accumulateCols ostar
\end{corollary}

\begin{proof}
Apply Lemma~\ref{lem:rectangle-decomposition} to Lemma~\ref{lem:a}.
\end{proof}


\begin{lemma}[Filter erasure]\hfill
< reduce oplus oplus x = if filled x then area x else 0
<   where
<     oplus 0 _ = 0
<     oplus _ 0 = 0
<     oplus a b = a + b
\end{lemma}

\begin{proof}
If |x| is not filled, then it contains a zero element. Therefore,
one of the |oplus| operations yields zero. The zero is propagated
by the surrounding |oplus|s so that the whole reduction becomes
zero.

If |x| is filled, then the reduction can be reduced to a single
series of |oplus| operations on |1|s. Since |oplus| behaves on
non-zero arguments like the ordinary |+|, the reduction yields the
element count of |x| which is equal to its area.
\end{proof}


\begin{theorem}\hfill
< foldl max 0 . map area . filter filled . rects

can be expressed as

< foldl max 0 . map (foldl max 0 . map (\ x -> length x * foldl min undefined x) . segs) . rows . accumulateCols ostar
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
