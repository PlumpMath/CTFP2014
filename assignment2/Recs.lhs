\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{thmtools}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{verbatim}
\usepackage{hyperref}
\bibliographystyle{acm}
\bibliography{ctfp}
\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
\declaretheorem[style=definition,qed=$\blacksquare$]{example}
\newcommand{\category}[1]{\mathcal{#1}}
\newcommand{\id}[0]{\mathrm{id}}
\newcommand{\coproduct}[2]{#1\!+\!#2}
\newcommand{\inl}[0]{\mathrm{inl}}
\newcommand{\inr}[0]{\mathrm{inr}}
\newcommand{\product}[2]{#1\!\times\!#2}
\newcommand{\fst}[0]{\mathrm{fst}}
\newcommand{\snd}[0]{\mathrm{snd}}
\newcommand{\pair}[2]{#1 \mathop{\triangle{}} #2}
\newcommand{\cross}[2]{#1\!\times{}\!#2}
\newcommand{\case}[2]{#1 \mathop{\triangledown{}} #2}
\newcommand{\either}[2]{#1\!+\!#2}
\newcommand{\inalg}[0]{\mathbf{in}}
\newcommand{\fold}[1]{\mathrm{fold}\,#1}
%include polycode.fmt


\begin{document}
\title{Recursion Schemes}
\author{People in the CTFP Course}
\maketitle
\tableofcontents

%include RecsZygomorphism.lhsinclude
\input{RecsMutumorphism.texinclude}
\input{RecsAccumulation.texinclude}
\input{RecsNestedDatatypes.texinclude}
\input{RecsIndexedDatatypes.texinclude}
\end{document}
