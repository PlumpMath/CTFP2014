\documentclass{scrartcl}
%include lhs2TeX.fmt
\usepackage{amsmath}
\usepackage{amsthm}
\newcommand\doubleplus{+\kern-1.3ex+\kern0.8ex}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\begin{document}

\begin{code}
import Prelude hiding ((**))
import Data.List
import Data.Ord

maxBy :: Ord b => (a -> b) -> a -> a -> a
maxBy f a b | f a >= f b = a
            | otherwise = b
\end{code}

Following the paper, we use the following definition of `segs':

\begin{code}
segs = map (foldr (++) [] . tails) . inits
\end{code}

The paper talks about computing the lengths of segments of the form:

\begin{code}
maxseg :: ([a] -> Bool) -> [a] -> [a]
maxseg p = foldr (maxBy length) [] . filter p . segs

maxtail p = foldr (maxBy length) [] . filter p . tails

\end{code}

\begin{code}
nodups :: Eq a => [a] -> Bool
nodups x = nub x == x

-- Naive implementation
dupfreeseg :: Eq a => [a] -> [a]
dupfreeseg = maxseg nodups
\end{code}

To optimize this naive implementation we introduce the
following property:

\begin{definition}
A predicate $p$ is prefix-closed iff
$p\ (xs \doubleplus ys) = p\ xs$ for all $xs$ and $ys$.
\end{definition}

\begin{lemma}
If $p$ is prefix-closed, then

\begin{code}
op p x a = foldr (maxBy length) [] . filter p . tails $ (x ++ [a]) 

maxtail' p = foldl (op p) []
\end{code}

and analogously:

\begin{code}
maxseg' p = foldr (maxBy length) . scanl (op p) []
\end{code}
\end{lemma}

\end{document}

