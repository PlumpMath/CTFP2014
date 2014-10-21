\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{parskip}
\usepackage{verbatim}
\bibliographystyle{acm}
\bibliography{ctfp}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
%include polycode.fmt

%format +++ = "\oplus "
%format *** = "\otimes "
%format ... = "\odot "
%format < = "\langle "
%format > = "\rangle "
%format forall = "\forall "
%format // = "\sswarrow"
%format \\ = "\ssearrow"
%format /\ = "\wedge "

\begin{document}
\title{Converting from Sequences to Heaps}
\author{People in the CTFP Course}
\maketitle
This document presents the problem of building a heap 
whose inorder traversal is a given sequence (Bird 1989) 
using a modern Haskell notation. We, however, use sumbols
to denote arbitrary binary operators for conciseness reasons.

We also rely on tree construction using partially defined binary 
operators for better readability. Thus the tree definition using ternary contructor
\begin{spec}
Tree a = Nil | Bin (Tree a) a (Tree a)
\end{spec}
can be rewritten as
\begin{spec}
Nil == < >
Bin l a r == l // <a> \\ r
\end{spec}
where $\langle \rangle$ denotes an empty tree 
and $\langle a \rangle$ a singleton tree.

\setcounter{section}{5}
\setcounter{subsection}{4}

\subsection{Accumulation lemma here}

%include HeapInorder.lhsinclude
%include HeapHeaptree.lhsinclude
%include HeapLeftfold.lhsinclude
%include HeapPaste.lhsinclude
%include Heapheapyheapy5point8.lhsinclude
\end{document}
