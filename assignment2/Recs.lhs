\documentclass{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{thmtools}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{verbatim}
\usepackage{hyperref}
\usepackage{tikz}
\usetikzlibrary{arrows,automata,matrix}
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

%format uF     = "\mu{}F"
%format inalg  = "\inalg"
%format fold f = "\fold{" f "}"

%format Bool  = "\mathsf{Bool}"
%format True  = "\mathbf{True}"
%format False = "\mathbf{False}"

%format Nat  = "\mathbb{N}"
%format Zero = "\mathbf{0}"
%format Succ = "\mathbf{1 +}"

%format fst       = "\fst{}"
%format snd       = "\snd{}"
%format pair  f g = "\pair{"   f "}{" g "}"
%format cross f g = "\cross{"  f "}{" g "}"
%format case_ f g = "\case{"   f "}{" g "}"
%format plus  f g = "\either{" f "}{" g "}"

%%format List A    = "[" A "]"
%%format Nil       = "[]"
%%format Cons a as = a "::" as

\newcommand{\ignore}[1]{}

\begin{document}
\ignore{
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}

module Recs where
\end{code}
}

\title{Recursion Schemes}
\author{People in the CTFP Course}
\maketitle
\tableofcontents

\ignore{
\begin{code}
pair :: (a -> b) -> (a -> c) -> (a -> (b , c))
pair f g a = (f a , g a)

cross :: (a -> c) -> (b -> d) -> ((a , b) -> (c , d))
cross f g (a , b) = (f a , g b)

case_ :: (a -> c) -> (b -> c) -> (Either a b -> c)
case_ = either

plus :: (a -> c) -> (b -> d) -> (Either a b -> Either c d)
plus f _ (Left  a) = Left  (f a)
plus _ g (Right b) = Right (g b)

class {- Functor f => -} Inalg f uF where
  -- The initial F-algebra.
  inalg :: f uF -> uF

  -- Given another F-algebra f, yields the unique arrow inalg → f.
  --
  -- > fold f . inalg == f . fmap f
  fold  :: (f a -> a) -> uF -> a

data FNat x  = Z     | S x
data Nat     = Zero  | Succ Nat
instance Inalg FNat Nat where
        inalg Z     = Zero
        inalg (S n) = Succ n

        fold f Zero     = f Z
        fold f (Succ n) = f (S (fold f n))
\end{code}
}

%include RecsZygomorphism.lhsinclude
\input{RecsMutumorphism.texinclude}
%include RecsMutumorphism.lhsinclude
\input{RecsAccumulation.texinclude}
\input{RecsNestedDatatypes.texinclude}
\input{RecsIndexedDatatypes.texinclude}
\end{document}
