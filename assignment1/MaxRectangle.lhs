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
> import qualified Data.List



> class Binoid a where
>   oplus :: a -> a -> a
>   otimes :: a -> a -> a

Satifsies
< (a oplus b) oplus c == a oplus (b oplus c)
< (a otimes b) otimes c == a otimes (b otimes c)

Satisfies
< (a oplus b) otimes (c oplus d) == (a otimes c) oplus (b otimes d)

> left, right :: a -> a -> a
> left  a _ = a
> right _ b = b

> newtype Left a = Left { mkLeft :: a }

> instance Binoid (Left a) where
>   oplus  = left
>   otimes = left

> dot :: Eq a => a -> a -> a
> dot a b = if a == b then a else undefined

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
> zipWith op (Above x y)   (Above x' y')  = zipWith op x x' `Above`  zipWith op y y'
> zipWith op (Beside x y)  (Beside x' y') = zipWith op x x' `Beside` zipWith op y y'

> -- See lecture notes 1.9 Segments
> segs :: [a] -> [[a]]
> segs = Prelude.foldr (++) [] . Prelude.map Data.List.tails . Data.List.inits

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


> -- See lecture notes 4.7 Directed reductions (⤈)
>
> singleExtract :: Array a -> a
> singleExtract (Singleton x) = x

> columnReduce :: (a -> a -> a) -> Array a -> Array a
> columnReduce f (Singleton z)             = Singleton z
> columnReduce f (Above x (Singleton y))   = Singleton $ singleExtract (columnReduce f x) `f` y
> columnReduce f (Beside x y)              = Beside    (columnReduce f x) (columnReduce f y)

> rowReduce :: (a -> a -> a) -> Array a -> Array a
> rowReduce f (Singleton z)             = Singleton z
> rowReduce f (Beside x (Singleton y))  = Singleton $ singleExtract (rowReduce f x) `f` y
> rowReduce f (Above x y)               = Above (rowReduce f x) (rowReduce f y)

Satisfy
< rows  == rowReduce Beside . map Singleton
< cols  == columnReduce Above . map Singleton


> -- See lecture notes 4.8 Accumulations

Considering the array element selectors/extractors

> bottomleft :: Array a -> a
> bottomleft = reduce right left

> topright :: Array a -> a
> topright = reduce left right

We define downward and rightward accumulations

> accumulateCols :: (a -> a -> a) -> Array a -> Array a
> accumulateCols f (Singleton z)            = Singleton z
> accumulateCols f (Above x (Singleton y))  = Above xs (Singleton (f (bottomleft xs) y))
>   where xs = accumulateCols f x
> accumulateCols f (Beside x y)             = Beside (accumulateCols f x) (accumulateCols f y)

> accumulateRows :: (a -> a -> a) -> Array a -> Array a
> accumulateRows f (Singleton z)             = Singleton z
> accumulateRows f (Beside x (Singleton y))  = Beside xs (Singleton (f (topright xs) y))
>   where xs = accumulateRows f x
> accumulateRows f (Above x y)               = Above (accumulateRows f x) (accumulateRows f y)

Satisfying
< listrows . (accumulateRows f)  == map (scanl f) . listrows
< listcols . (accumulateCols f)  == map (scanl f) . listcols

Similarly, we can define accumulations in the opposite directions (i.e.: upwards and leftwards)

> accumulateColsUp :: (a -> a -> a) -> Array a -> Array a
> accumulateColsUp f (Singleton z)            = Singleton z
> accumulateColsUp f (Above (Singleton y) x)  = Above (Singleton (f (topright xs) y)) xs
>   where xs = accumulateColsUp f x
> accumulateColsUp f (Beside x y)             = Beside (accumulateColsUp f x) (accumulateColsUp f y)

> accumulateRowsLeft :: (a -> a -> a) -> Array a -> Array a
> accumulateRowsLeft f (Singleton z)             = Singleton z
> accumulateRowsLeft f (Beside (Singleton y) x)  = Beside (Singleton (f (bottomleft xs) y)) xs
>   where xs = accumulateRowsLeft f x
> accumulateRowsLeft f (Above x y)               = Above (accumulateRowsLeft f x) (accumulateRowsLeft f y)


> -- See lecture notes 4.9 Tops and bottoms

In a similar fashion to inits

> lefts :: Array a -> Array (Array a)
> lefts = accumulateRows Beside . cols

> tops :: Array a -> Array (Array a)
> tops = accumulateCols Above . rows

And then to tails

> rights :: Array a -> Array (Array a)
> rights = accumulateRowsLeft Beside . cols

> bottoms :: Array a -> Array (Array a)
> bottoms = accumulateColsUp Above . rows

\begin{lemma}[Accumulation lemma]
\label{lem:accum}
Certain reduction computations can be re-expressed into accumulations:
< map (columnReduce oplus)  . tops     = rows  . accumulateCols oplus
< map (rowReduce oplus)     . lefts    = cols  . accumulateRows oplus
< map (columnReduce oplus)  . bottoms  = rows  . accumulateColsUp oplus
< map (rowReduce oplus)     . rights   = cols  . accumulateRowsLeft oplus

\end{lemma}

\begin{proof}
Given the orthogonal reduction rules
< map (columnReduce oplus)  . lefts    = lefts    . columnReduce oplus
< map (rowReduce oplus)     . tops     = tops     . rowReduce oplus
< map (columnReduce oplus)  . rights   = rights   . columnReduce oplus
< map (rowReduce oplus)     . bottoms  = bottoms  . rowReduce oplus

and the orthogonal accumulation rules
< map (accumulateCols oplus)  . lefts    = lefts    . accumulateCols oplus
< map (accumulateRows oplus)  . tops     = tops     . accumulateRows oplus
< map (accumulateCols oplus)  . rights   = rights   . accumulateCols oplus
< map (accumulateRows oplus)  . bottoms  = bottoms  . accumulateRows oplus

By definition of |tops|
< map (columnReduce oplus) . tops = map (columnReduce oplus) . accumulateCols Above . rows

From which, given the reduction and accumulation occur in the same dimension
it is simple to see the first accumulation equality holds. Similarly for the
third equality.

In an analogue way, for the second equality, the definition of |lefts| means
< map (rowReduce oplus) . lefts = map (rowReduce oplus) . accumulateRows Beside . cols

Again with reductions and accumulation happening in the same dimension (as
happens in the fourth equality).

\end{proof}



\begin{lemma}[Horner's rule]
\label{lem:horner}
Analogue of Horner's rule for arrays:

< reduce oplus oplus . map (reduce otimes odot) . bottoms

It is necessary that otimes distributes over oplus and oplus abides with odot.
These properties allow one to prove that:

< reduce oplus oplus . map (reduce otimes odot) . bottoms = reduce odot odot .  rowReduce ostar

Where ostar is defined as:

> ostar :: Binoid a => a -> a -> a
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
