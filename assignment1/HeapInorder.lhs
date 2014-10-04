\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{parskip}
\usepackage{verbatim}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
%include polycode.fmt

%format +++ = "\oplus "
%format < = "\langle "
%format > = "\rangle "
%format forall = "\forall "
%format // = "\sswarrow"
%format \\ = "\ssearrow"
%format <-> = "\Leftrightarrow"

\begin{document}
We begin by translating the unoptimized definition
of $heap$:

\begin{definition}
We define a naive implementation of $heap$ as follows:

\begin{spec}
heap = foldr (+++) < > . map (\x -> < x >)
< > +++ t = t
t +++ < > = t
(x // < a > \\ y) +++ (u // < b > \\ v)
    | a < b = x // < a > \\ (y +++ (u // < b > \\ v))
    | otherwise = ((x // < a > \\ y) +++ u) // < b > \\ v
\end{spec}
\end{definition}

\begin{theorem}\label{thm:inorder}
< forall xs: inorder (heap xs) = xs
\end{theorem}

To prove this, we first establish the following auxiliary lemma:

\begin{lemma}\label{lem:inorder}
For every $a$ and every tree $t$, the
following holds:

< inorder (< a > +++ t) == [a] ++ inorder t
\end{lemma}

\begin{proof}
We prove the statement by induction on $t$:

Case $\langle \rangle$ is trivial:

\textbf{Case} $u \sswarrow \langle b \rangle \ssearrow v$:
We distinguish the cases $a < b$ and $a \ge b$:

\textbf{Case} $a < b$:
In this case we have:
\begin{spec}
inorder (< a > +++ u // < b > \\ v) == -- by definition of +++
inorder (< a > \\ (u // < b > \\ v)) == -- by definition of $inorder$
treeFold (++) (++) [] . treeMap (:[]) $ < a > \\ (u // < b > \\ v)
== -- by definitions of $treeFold$ and $foldMap$
[a] ++ treeFold (++) (++) [] . treeMap (:[]) $ u // < b > \\ v
== -- by definition of $inorder$
[a] ++ inorder (u // < b > \\ v)
\end{spec}

\textbf{Case} $a \ge b$:
\begin{spec}
inorder ((< a > +++ u) // < b > v) == -- by definition of +++
inorder ((< a > +++ u) // < b > \\ v) == -- by definition of $inorder$
treeFold (++) (++) [] . treeMap (:[]) $ (< a > +++ u) // (< b > \\ v)
== -- by definition of $treeFold$ and $treeMap$
(treeFold (++) (++) [] . treeMap (:[]) $ (< a > +++ u)) ++
(treeFold (++) (++) [] . treeMap (:[]) $ < b > \\ v)
== -- by definition of $inorder$:
inorder (< a > +++ u) ++ inorder (< b > \\ v)
== -- by induction hypothesis:
[a] ++ inorder u ++ inorder (< b > \\ v)
== -- by properties of $inorder$:
[a] ++ inorder (u // < b > \\ v)
\end{spec}
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:inorder}]
We proceed by induction on $xs$:

\textbf{Case} $[]$: Trivial.

\textbf{Case} $x : xs$:
\begin{spec}
inorder (heap (x : xs)) == -- definition of $heap$:
inorder (foldr (+++) < > . map (\x -> < x >) $ x : xs) == -- definition of $map$:
inorder (foldr (+++) < > .$ < x > : map (\x -> < x >) xs) == -- by definition of $foldr$:
inorder (< x > +++ foldr (+++) <  > (map (\x -> < x >) xs)) == -- by Lemma~\ref{lem:inorder}
[ x ] ++ inorder (foldr (+++) <  > (map (\x -> < x >) xs)) == -- definition of $heap$:
[ x ] ++ inorder (heap xs) == -- by induction hypothesis
[ x ] ++ xs == -- by definition of ++
x : xs
\end{spec}
\end{proof}

\end{document}
