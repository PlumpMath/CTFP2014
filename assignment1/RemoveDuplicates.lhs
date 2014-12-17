\documentclass{scrartcl}
%include lhs2TeX.fmt
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{hyperref}
\usepackage[numbers]{natbib}

\newcommand\doubleplus{+\kern-1.3ex+\kern0.8ex}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\parindent 0pt\parskip 0.5ex
\title{Longest duplicate-free list segment}
\begin{document}
\maketitle

First, we import required libraries and define some
auxiliary functions.

\begin{code}
import Data.List
import Data.Ord

maxBy :: Ord b => (a -> b) -> a -> a -> a
maxBy f a b  | f a >= f b  = a
             | otherwise   = b
\end{code}

Following Bird's paper \citep{Bird1987}, we use the following definition of |segs|:

\begin{code}
segs = map (foldr (++) [] . tails) . inits
\end{code}

The function returns all segments of a finite list.

The paper talks about computing longest segment of a list, 
which satisfy some property |p|, using functions:

\begin{code}
maxinit  p  = foldr (maxBy length) [] . filter p . inits
maxtail  p  = foldr (maxBy length) [] . filter p . tails
maxseg   p  = foldr (maxBy length) [] . filter p . segs
\end{code}

These functions all have the same type: 
\begin{code}
maxinit, maxtail, maxseg :: ([a] -> Bool) -> [a] -> [a]
\end{code}
and check property for, respectively, initial, final and \emph{all} segments of a list.

Assuming that checking whether predicate |p| holds takes $O(n^k)$ steps for a $n$-element list,
we will need $O(n^{k+1})$ steps for computing |maxinit| and |maxtail|,
and $O(n^{k+2})$ for |maxseg|.
  
For example, consider a problem of finding a longest duplicate-free segment of list, 
specified as follows:  
 
\begin{code}
-- Our predicate
nodups :: Eq a => [a] -> Bool
nodups x = nub x == x

-- Naive implementation
dupfreeseg :: Eq a => [a] -> [a]
dupfreeseg = maxseg nodups
\end{code}

Since $nodups$ takes $O(n^2)$ steps for a list with $n$ elements, this
computation requires $O(n^4)$ steps in total.

However, according to Bird \citep{Bird1987}, complexity of longest-segment functions 
can be reduced by imposing additional restrictions on the predictes involved.

First, we introduce the following properties:

\begin{definition}
A predicate |p| is \emph{prefix-closed} iff
|p (xs ++ ys) = p xs| for all |xs| and |ys|.
\end{definition}

\begin{definition}
A predicate |p| is \emph{suffix-closed} iff
|p (xs ++ ys) = p ys| for all |xs| and |ys|.  
\end{definition}

\begin{definition}
  A predicate |p| is \emph{segment-closed} iff
  it is both prefix-closed and suffix-closed, i.e.:
  |p (xs ++ ys) = p xs && p ys|
\end{definition}

\begin{lemma}
\label{lem:prefixclosed}
If $p$ is prefix-closed, then |maxtail p = maxtail' p| for:

\begin{code}
op p x a = foldr (maxBy length) [] . filter p . tails $ (x ++ [a]) 

maxtail' p = foldl (op p) []
\end{code}

and hence:

\begin{code}
maxseg' p = foldr (maxBy length) [] . scanl (op p) []
\end{code}
\end{lemma}

If we assume that checking whether |p| holds, takes $O(n^k)$ steps,
the preceding lemma allows us to compute |maxseg'| in $O(n^{k+1})$ steps.

So now we can come up with an $O(n^3)$ solution to our problem.

\begin{code}
-- same as `maxseg nodups`
naiveNoDups :: Eq a => [a] -> [a]
naiveNoDups = foldr (maxBy length) [] . filter nodups . segs

-- same as maxseg' nodups
fasterNoDups :: Eq a => [a] -> [a]
fasterNoDups = foldr (maxBy length) [] . scanl (op nodups) [] 
\end{code}

However, we can decrease the running time even further by making use of the
fact that, in this case, |p| is segment-closed:

\begin{lemma}
\label{lem:segmentclosed}
  If |p| is segment-closed, holds for all singleton lists and satisfies:

  |p (x ++ [a]) = p x && q a x|

  For some |q|, then |maxtail p = maxtail'' q| for:

\begin{code}
maxtail'' :: (a -> [a] -> Bool) -> [a] -> [a]
maxtail'' q = foldl (op' q) []

-- where:
op' q xs a = (foldr (maxBy length) [] . filter (q a) $ tails xs) ++ [a]
\end{code}

Therefore |maxsegs = maxsegs''| for:

\begin{code}
maxsegs'' :: (a -> [a] -> Bool) -> [a] -> [a]
maxsegs'' q = foldr (maxBy length) [] . scanl (op' q) []
\end{code}

\end{lemma}

One can show that if |q| has complexity $O(n^k)$, then
we can compute |maxsegs'' q xs| in $O(n^{k+1})$ steps.

Note that |nodups| is segment-closed and holds for all singleton lists. Moreover,
the following holds
%**TODO Keep replacing $some program$ with |some program| or code blocks or spec blocks

\[ nodups\ (xs \doubleplus [a]) = nodups\ xs \land all\ (\not\equiv a)\ xs \]

I.e., we can instantiate $q$ with $\lambda xs\ a. all\ (\not\equiv a)\ xs$ in
Lemma~\ref{lem:segmentclosed}. Clearly, we can compute $all (\neq a)\ xs$ in
$O(n)$ steps where $n$ is the length of $xs$. Hence, we can compute
the longest duplicate-free segment of a list in $O(n^2)$ steps as follows:

\begin{code}
quadraticNoDups :: Eq a => [a] -> [a]
quadraticNoDups = maxsegs'' (\a xs -> all (/= a) xs)
\end{code}

\bibliographystyle{acm}
\bibliography{../ctfp}

\end{document}

