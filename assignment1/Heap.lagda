\documentclass{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include agda.fmt

\usepackage{textgreek}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{graphicx}
\usepackage{fancyvrb}
\usepackage{hyperref}
\usepackage{color}


\usepackage{tikz}

\usetikzlibrary{cd}
\usetikzlibrary{arrows, matrix, trees}
\tikzcdset{every diagram/.style={column sep=4cm, row sep=4cm}}

\begin{document}

\title{}
\author{}

%if False
\begin{code}
module Heap where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Function
\end{code}
%endif

\section{Trees}

\begin{code}
data Tree (A : Set) : ℕ → Set where
  ⟨⟩  : Tree A 0
  ⟨_⟩ : A → Tree A 1
  _↙_ : ∀ {n m} → Tree A n → Tree A (suc m) → Tree A (n + suc m)
  _↘_ : ∀ {n m} → Tree A (suc n) → Tree A m → Tree A (suc n + m)
\end{code}

\section{Maps and reduces}

\begin{code}
map-tree : ∀ {A B n} → (A → B) → Tree A n → Tree B n
map-tree f ⟨⟩ = ⟨⟩
map-tree f ⟨ x ⟩ = ⟨ f x ⟩
map-tree f (x ↙ y) = map-tree f x ↙ map-tree f y
map-tree f (x ↘ y) = map-tree f x ↘ map-tree f y

record Reducer A : Set where
  field
    ⊕ : A → A → A
    ⊗ : A → A → A
    e : A

reduce-tree : ∀ {A n} → Reducer A → Tree A n → A
reduce-tree r ⟨⟩ = Reducer.e r
reduce-tree r ⟨ x ⟩ = x
reduce-tree r (x ↙ y) = (Reducer.⊕ r) (reduce-tree r x) (reduce-tree r y)
reduce-tree r (x ↘ y) = (Reducer.⊗ r) (reduce-tree r x) (reduce-tree r y)
\end{code}

\subsection{Examples}

\begin{code}
_<<_   : ∀ {A : Set} → A → A → A
a << b = a

_>>_   : ∀ {A : Set} → A → A → A
a >> b = b

label : ∀ {A n} → A → Tree A n → A
label def = reduce-tree (record { ⊕ = _>>_ ; ⊗ = _<<_ ; e = def })

inorder : ∀ {A n} → Tree A n → List A
inorder = reduce-tree (record { ⊕ = _++_ ; ⊗ = _++_ ; e = [] }) ∘ map-tree ([_])

size : ∀ {A n} → Tree A n → ℕ
size = reduce-tree (record { ⊕ = _+_ ; ⊗ = _+_ ; e = 0 }) ∘ map-tree (λ x → 1)

member : ∀ {A n} → A → Tree A n → Bool
member x = reduce-tree (record { ⊕ = _∧_ ; ⊗ = _∧_ ; e = true }) ∘ map-tree {!!}

depth : ∀ {A n} → Tree A n → ℕ
depth = reduce-tree (record { ⊕ = λ a b → suc a ⊔ b ; ⊗ = λ b a → suc a ⊔ b ; e = 0 }) ∘ map-tree (λ x → 1)

heaporder : ∀ {A n} → Tree A n → List A
heaporder = reduce-tree (record { ⊕ = {!!} ; ⊗ = {!!} ; e = [] }) ∘ map-tree ([_])
\end{code}

\section{Accumulations}

\begin{code}

\end{code}

\section{Building a heap}

\begin{code}

\end{code}

\section{Solution as a left reduction}

\begin{code}

\end{code}

\section{Prefix and suffix}

\begin{code}

\end{code}

\section{A linear algorithm}

\begin{code}

\end{code}

\section{Application}

\begin{code}

\end{code}


\end{document}
