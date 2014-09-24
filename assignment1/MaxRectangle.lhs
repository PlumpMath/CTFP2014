\documentclass{article}
%include polycode.fmt
%format ostar = "\oast "
%format oplus = "\oplus "
%format * = "\cdot "

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
> rows :: Array a -> [Array a]
> rows = undefined

> -- See lecture notes 4.7 Directed reductions (⤈)
> directedReduce :: (a -> a -> a) -> Array a -> Array a
> directedReduce = undefined

> -- See lecture notes 4.8 Accumulations (⇟)
> accumulate :: (a -> a -> a) -> Array a -> Array a
> accumulate = undefined

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
> r' = foldl max 0 . Prelude.map h . rows . accumulate ostar
>   where
>     h = foldl max 0 . Prelude.map f . segs
>     f x = width x * reduce min min x

>     oplus 0 _ = 0
>     oplus _ 0 = 0
>     oplus a b = a + b

>     ostar :: Int -> Int -> Int
>     ostar a b = max (a `oplus` b) b


\begin{lemma}[Rectangle decomposition]
If for some |g|, |ostar|

< reduce oplus oplus . map f . bottoms = g . directedReduce ostar

then

< reduce oplus oplus . map f . rects = reduce oplus oplus . map h . rows . accumulate ostar
<   where
<     h = reduce oplus oplus . map g . vsegs
\end{lemma}

\begin{proof}
missing
\end{proof}


\begin{lemma}\hfill
< reduce max max . map (reduce oplus oplus) . bottoms

can be expressed as

< (\ x -> width x * foldl min undefined x) . directedReduce ostar
\end{lemma}

\begin{proof}
missing
\end{proof}


\begin{corollary}\hfill
< reduce max max . map (reduce oplus oplus) . rects

can be expressed as

< reduce max max . map (reduce max max . map g . vsegs) . rows . accumulate ostar
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

< fold max . map (foldl max 0 . map (\ x -> length x * foldl min undefined x) . segs) . rows . accumulate ostar
\end{theorem}

\begin{proof}\hfill
< foldl max 0 . map area . filter filled . rects

= Filter erasure (OBS: the result for empty arrays is zero, was -∞ before)

< reduce max max . map (reduce oplus oplus) . rects

= Rectangle decomposition

< foldl max 0 . map (foldl max 0 . map (\ x -> width x * foldl min undefined x) . vsegs) . rows . accumulate ostar

= On lists

< foldl max 0 . map (foldl max 0 . map (\ x -> length x * foldl min undefined x) . segs) . rows . accumulate ostar
\end{proof}


\begin{corollary}
The largest filled rectangle can be computed in linear time.
\end{corollary}

\begin{proof}
missing
\end{proof}
\end{document}
