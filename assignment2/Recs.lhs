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
\usepackage{xypic}
\usetikzlibrary{arrows,automata,matrix}
%\bibliographystyle{acm}
%\bibliography{ctfp}
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

%format Mu     = "\mu{}"
%%format Mu F  = "\mu{}" F
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
{-# LANGUAGE DeriveFunctor #-}

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

-- functor f, carrier a
type Algebra f a = f a -> a

-- the (!) fix point of f
--
-- < M . unM == id :: Mu f     -> Mu f
-- < unM . M == id :: f (Mu f) -> f (Mu f)
newtype Mu f = M { unM :: f (Mu f) }

inalg :: Algebra f (Mu f)
inalg = M

fold, cata :: Functor f => Algebra f a -> (Mu f -> a)
fold f (M x)  = f (fmap (fold f) x)
cata f        = fold f
--cata f = para (f . fmap fst)

para :: Functor f => (f (a , Mu f) -> a) -> (Mu f -> a)
para f = fst . fold (pair f (inalg . fmap snd))
--para f = zygo f inalg

zygo :: Functor f => (f (a , b) -> a) -> Algebra f b -> (Mu f -> a)
zygo f h = fst . fold (pair f (h . fmap snd))
--zygo f h = fst . mutu f (h . fmap snd)

mutu :: Functor f => (f (a , b) -> a) -> (f (a , b) -> b) -> (Mu f -> (a , b))
mutu f g = fold (pair f g)

data FNat x  = Zero  | Succ x deriving Functor
type Nat     = Mu FNat
\end{code}
}

%include RecsZygomorphism.lhsinclude
\input{RecsMutumorphism.texinclude}
%include RecsMutumorphism.lhsinclude
%include RecsAccumulation.lhsinclude
\input{RecsNestedDatatypes.texinclude}
%include RecsNestedDatatypes.lhsinclude
\input{RecsIndexedDatatypes.texinclude}
\end{document}
