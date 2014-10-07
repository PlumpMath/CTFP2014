\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{parskip}
\usepackage{verbatim}
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
%format // = "\sswarrow"
%format \\ = "\ssearrow"
%format /\ = "\wedge "

\begin{document}
\title{Converting from Sequences to Heaps}
\author{People in the CTFP Course}
\maketitle
%include HeapInorder.lhsinclude
%include HeapLeftfold.lhsinclude
\end{document}
