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
\usepackage{parskip}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}{Corollary}
\newtheorem{example}{Example}

\begin{document}
\textit{By Daniel O, Irene, Pablo, Fabian and Jeremy.}

\section{Max Rectangle}
Given an array |x| with elements from the set of booleans. We are to find an
efficient algorithm that computes the area of the largest rectangle of |x|
whose elements all are true.

> module MaxRectangle where

\subsection{Prerequisites}

> import qualified Prelude
> import Prelude hiding (Left, map, zipWith)
> import qualified Data.List

We define a type class \emph{Binoid},

> class Binoid a where
>   oplus :: a -> a -> a
>   otimes :: a -> a -> a

with the additional requirement that |oplus| and |otimes| are associative and
also satisfy the equation

< (a oplus b) otimes (c oplus d) = (a otimes c) oplus (b otimes d)

We can define an example binoid with the |left| and |right| functions (similar
to |fst| and |snd| but for curried functions)

> left, right :: a -> a -> a
> left  a _ = a
> right _ b = b

> newtype Left a = Left { mkLeft :: a }

> instance Binoid (Left a) where
>   oplus = left
>   otimes = left

We also need a partial function |dot| which only is defined if its arguments
are equal

> dot :: Eq a => a -> a -> a
> dot a b = if a == b then a else undefined

\subsection{Arrays}

A multidimensional array can be defined as

\begin{definition}[Array]\hfill
\label{def:array}

> data Array a
>   = Singleton a
>   | Above (Array a) (Array a)
>   | Beside (Array a) (Array a)
>   deriving Show

> (|||) :: Array a -> Array a -> Array a
> (|||) = Beside

> (|-|) :: Array a -> Array a -> Array a
> (|-|) = Above

> lift :: a -> Array a
> lift a = Singleton a

Two functions |width| and |height| defines restrictions for well-formedness of
an array. |Above x y| is defined iff |width x == width y| and |Beside x y| is
defined iff |height x == height y|.

> height :: Array a -> Int
> height (Singleton _) = 1
> height (Above x y)   = height x + height y
> height (Beside x y)  = height x `dot` height y

> width :: Array a -> Int
> width (Singleton _) = 1
> width (Above x y)   = width x `dot` width y
> width (Beside x y)  = width x + width y

\end{definition}


\subsection{Map}
The array homomorphism |map| is given by the equations

> map :: (a -> b) -> Array a -> Array b
> map f (Singleton a) = Singleton $ f a
> map f (Above x y)   = map f x `Above` map f y
> map f (Beside x y)  = map f x `Beside` map f y

Distributivity of |map| holds the same for arrays as for lists,

< map (f . g) = map f . map g

We also have that

< height (map f x) = height x
< width (map f x) = width x

\subsection{Reduce}

Array reduction is defined using two operators and the equations

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


\subsection{Directed reduction}

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


\subsection{Accumulations}

Considering the array element selectors/extractors

> bottomleft :: Array a -> a
> bottomleft = reduce right left

> topright :: Array a -> a
> topright = reduce left right

We define downward and rightward accumulations

> topAccumulation :: (a -> a -> a) -> Array a -> Array a
> topAccumulation f (Singleton z)            = Singleton z
> topAccumulation f (Above x (Singleton y))  = Above xs (Singleton (f (bottomleft xs) y))
>   where xs = topAccumulation f x
> topAccumulation f (Beside x y)             = Beside (topAccumulation f x) (topAccumulation f y)

> accumulateRows :: (a -> a -> a) -> Array a -> Array a
> accumulateRows f (Singleton z)             = Singleton z
> accumulateRows f (Beside x (Singleton y))  = Beside xs (Singleton (f (topright xs) y))
>   where xs = accumulateRows f x
> accumulateRows f (Above x y)               = Above (accumulateRows f x) (accumulateRows f y)

Satisfying
< listrows . (accumulateRows f)  == map (scanl f) . listrows
< listcols . (topAccumulation f)  == map (scanl f) . listcols

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


\subsection{Segments: tops \& bottoms, lefts \& rights}

In a similar fashion to inits

> lefts :: Array a -> Array (Array a)
> lefts = accumulateRows Beside . cols

> tops :: Array a -> Array (Array a)
> tops = topAccumulation Above . rows

And then to tails

> rights :: Array a -> Array (Array a)
> rights = accumulateRowsLeft Beside . cols

> bottoms :: Array a -> Array (Array a)
> bottoms = accumulateColsUp Above . rows

\begin{lemma}[Accumulation lemma]
\label{lem:accum}
Certain reduction computations can be re-expressed into accumulations:
< map (columnReduce oplus)  . tops     = rows  . topAccumulation oplus
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
< map (topAccumulation oplus)  . lefts    = lefts    . topAccumulation oplus
< map (accumulateRows oplus)  . tops     = tops     . accumulateRows oplus
< map (topAccumulation oplus)  . rights   = rights   . topAccumulation oplus
< map (accumulateRows oplus)  . bottoms  = bottoms  . accumulateRows oplus

By definition of |tops|
< map (columnReduce oplus) . tops = map (columnReduce oplus) . topAccumulation Above . rows

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

\begin{example}[Horner's rule]
\begin{equation*}
x = \begin{pmatrix}
    1 & 2 \\
    3 & 4 \\
    5 & 6 \\
\end{pmatrix}
\end{equation*}

LHS:

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

\begin{spec}

  ((1 `otimes` 3 `otimes` 5) `odot` (2 `otimes` 4 `otimes` 6)) `oplus` ((3 `otimes` 5) `odot` (4 `otimes` 6)) `oplus` (5 `odot` 6)

= {- oplus and odot abide -}

  ((1 `otimes` 3 `otimes` 5) `oplus` (3 `otimes` 5) `oplus` 5) `odot` ((2 `otimes` 4 `otimes` 6) `oplus` (4 `otimes` 6) `oplus` 6)

= {- distribution of otimes over oplus -}

  ((((1 `otimes` 3) `oplus` 3) `otimes` 5) `oplus` 5) `odot` ((((2 `otimes` 4) `oplus` 4) `otimes` 6) `oplus` 6)

= {- use ostar to simplify -}

  ((1 `ostar` 3) `ostar` 5) `odot` ((2 `ostar` 4) `ostar` 6)

= {- and finally -}

  reduce odot odot (rowReduce ostar x)
\end{spec}

which is the RHS.
\end{example}


Top-lefts of an array.  Analogous to ``inits'' for lists.

> topls :: Array a -> Array (Array a)
> topls = reduce (|-|) (|||) . map tops . lefts

\begin{example}[Top-lefts of an array]
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
\end{example}

Bottom rights, like ``tails''.

> botrs :: Array a -> Array (Array a)
> botrs = reduce (|-|) (|||) . map bottoms . rights

Horizontal segments:

> hsegs :: Array a -> Array (Array a)
> hsegs = reduce (|-|) (|||) . map bottoms . tops

Vertical segments:

> vsegs :: Array a -> Array (Array a)
> vsegs = reduce (|-|) (|||) . map rights . lefts

\begin{definition}[Rectangle]
\label{def:rectangle}

One way of defining the rectangles:

> rects :: Array a -> Array (Array a)

< rects = reduce (|-|) (|||) . map botrs . topls

Another way:

> rects = reduce (|-|) (|||) . map hsegs . vsegs

\end{definition}



> -- See lecture notes 4.14 Application
> area :: Array a -> Int
> area = reduce (+) (+) . map (const 1)

> -- See lecture notes 4.14 Application
> filled :: Array Int -> Bool
> filled = reduce (&&) (&&) . map (== 1)

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
<    reduce (oplus) (oplus) . map h . rows . topAccumulation (ostar)
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
  reduce (oplus) (oplus) . map h . rows . topAccumulation (ostar)
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
\def\commentbegin{\quad\{\ }
\def\commentend{\}}

\begin{spec}
  reduce max max . map (reduce oplus oplus) . bottoms

= {- $x \in \{ 0, 1 \}^{n \times m}$: |reduce oplus oplus x = width x * reduce oplus min x| -}

  reduce max max . map (\ y -> width y * reduce oplus min y) . bottoms

= {- all bottoms have the same width -}

  reduce max max $ map (\ y -> width x . reduce oplus min y) $ bottoms x

= {- map distributivity -}

  reduce max max $ map (width x *) $ map (reduce oplus min) $ bottoms x

= {- the width is a positive number -}

  width x * (reduce max max . map (reduce oplus min) . bottoms) x

= {- Horner's rule: |oplus| distributes through |max|, and |min| abides with |oplus| -}

  width x * (reduce min min . columnReduce ostar) x

= {- |columnReduce| preserves the width -}

  (\ x -> width x * reduce min min x) . columnReduce ostar
\end{spec}
\end{proof}


\begin{corollary}\hfill
\label{lem:b}

> b = reduce max max . map (reduce oplus oplus) . rects
>   where
>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b

can be expressed as

> b' = reduce max max . map (reduce max max . map g . vsegs) . rows . accumulateCols ostar
>   where
>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b
>
>     g x = width x * reduce min min x
>     ostar a b = max (a `oplus` b) b

\end{corollary}

\begin{proof}
Apply Lemma~\ref{lem:rectangle-decomposition} to Lemma~\ref{lem:a}.
\end{proof}


\begin{lemma}[Filter erasure]\hfill
\label{lem:filter-erasure}

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


\begin{theorem}
\label{thm:r=r'}

The MaxRectangle algorithm

> r  = foldl max 0 . Prelude.map area . filter filled . bag . rects
>   where
>     bag = reduce (++) (++) . map (\ x -> [x])

can be expressed as

> r' = foldl max 0 . Prelude.map h . listrows . accumulateCols ostar
>   where
>     h = foldl max 0 . Prelude.map f . segs
>     f x = length x * foldl min 1 x
>
>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b
>
>     ostar a b = max (a `oplus` b) b

\end{theorem}

\begin{proof}
We start with the naive solution of MaxRectangle.

< foldl max 0 . Prelude.map area . filter filled . bag . rects

Because of the very restrictive set of array elements we can apply
lemma~\ref{lem:filter-erasure} and, thereby, erase the filter step
from the algorithm.

< reduce max max . map (reduce oplus oplus) . rects

Here, we accept that the result for empty arrays will be zero, while
it used to be the negative infinity with the previous implementation.
From the standpoint of the empty array containing the empty rectangle
with area 0 this makes quite some sense.

Now, lemma~\ref{lem:b} as a particular instance of rectangle
decomposition says that we can also save us from computing all
rectangles in the input array. It is enough to first look at the
columns and then at the rows.

< reduce max max
<   . map (reduce max max
<            . map (\ x -> width x * reduce min min x)
<            . vsegs)
<   . rows
<   . accumulateCols ostar

The last step doesn't seem obvious at all and is, therefore, split up
into several lemmata.

Lastly, we turn our backs on arrays in favor of lists as soon as
possible in the implementation. This is, at least intuitively,
correct since rows are arrays of height 1.

< foldl max 0
<   . Prelude.map (foldl max 0
<                    . Prelude.map (\ x -> length x * foldl min 1 x)
<                    . segs)
<   . listrows
<   . accumulateCols ostar

This concludes our proof.
\end{proof}


\begin{corollary}
The largest filled rectangle can be computed in linear time.
\end{corollary}

\begin{proof}
Since |r'| from theorem~\ref{thm:r=r'} is in some sense equivalent to
the naive solution |r| of MaxRectangle, it computes the largest
filled rectangle in $0,1$-arrays.

Furthermore, the operator |otimes| is computable in constant time
and, therefore, the accumulation part takes a number of steps
proportional to the number of elements in the input array. |h| can be
shown to be computable in linear time (missing) as well. Since
|foldl| and |map|, which are also used to implement |listrows|, need
only time linear in the length of their input, |r'| as a whole is
computable in time linear in the number of array elements.
\end{proof}
\end{document}
