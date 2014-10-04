\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
%include polycode.fmt

%format +++ = "\oplus "
%format *** = "\otimes "
%format < = "\langle "
%format > = "\rangle "
%format forall = "\forall "
%format /\ = "\wedge "

\begin{document}
\begin{definition}
The implementation of the heap build function from the lecture notes.

< heap' = foldl (***) < >
<   where
<     u *** a = u +++ < a >
\end{definition}

The lecture notes actually talk only about a left fold implementation
(here, |heap'|) of the heap build function. However, we prove the
|inorder| and |heaptree| specification for an implementation that
composes |foldr| with |map| (here, |heap|) instead, and show that the
lecture notes implementation is equivalent.

\begin{theorem}\label{thm:leftfold}
The definitions of |heap| and |heap'| are equivalent.

< forall xs: heap xs == heap' xs
\end{theorem}

\begin{proof}
By induction on |xs| we first show:

< forall e xs: foldl (+++) e . map (\x -> < x >) $ xs == foldl (***) e xs

\textbf{Case} |[]|: Trivial. Both folds evaluate to |e|.

\textbf{Case} |x : xs|:
\begin{spec}
foldl (+++) e . map (\x -> < x >) $ x : xs == -- definition of |map|
foldl (+++) e $ < x > : map (\x -> < x >) xs == -- definition of |foldl|
foldl (+++) (e (+++) < x >) $ map (\x -> < x >) xs == -- induction hypothesis
foldl (***) (e (+++) < x >) xs == -- definition of |(***)|
foldl (***) (e (***) x) xs == -- definition of |foldl|
foldl (***) e (x : xs)
\end{spec}

Using this identity we prove the theorem:

\begin{spec}
heap (x : xs) == -- definition of $heap$
foldr (+++) < > . map (\x -> < x >) $ x : xs == -- associativity of |(+++)|
foldl (+++) < > . map (\x -> < x >) $ x : xs == -- !
foldl (***) < > (x : xs) == -- definition of |heap'|
heap' (x : xs)
\end{spec}
\end{proof}

\begin{corollary}\label{cor:buildfunction}
|heap'| is a right-inverse of |inorder| and the trees it returns are
in fact heaps.

< forall xs: inorder (heap' xs) == xs /\ heaptree (heap' xs) == true
\end{corollary}

\begin{proof}
This follows from the fact that the result holds for |heap| which was
shown to be equivalent to |heap'|.
\end{proof}
\end{document}
