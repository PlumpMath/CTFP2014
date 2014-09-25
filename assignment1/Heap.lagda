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
open import Relation.Binary.Core
\end{code}
%endif

\section{Trees}

\begin{code}
data Tree (A : Set) : Bool → Set where
  ⟨⟩  : Tree A false
  ⟨_⟩ : A → Tree A true
  _↙_ : ∀ {b} → Tree A b → Tree A true → Tree A true
  _↘_ : ∀ {b} → Tree A true → Tree A b → Tree A true
\end{code}

\section{Maps and reduces}

\begin{code}
map-tree : ∀ {A B b} → (A → B) → Tree A b → Tree B b
map-tree f ⟨⟩ = ⟨⟩
map-tree f ⟨ x ⟩ = ⟨ f x ⟩
map-tree f (x ↙ y) = map-tree f x ↙ map-tree f y
map-tree f (x ↘ y) = map-tree f x ↘ map-tree f y

record Reducer A : Set where
  field
    ⊕ : A → A → A
    ⊗ : A → A → A
    e : A

reduce-tree : ∀ {A b} → Reducer A → Tree A b → A
reduce-tree r ⟨⟩ = Reducer.e r
reduce-tree r ⟨ x ⟩ = x
reduce-tree r (x ↙ y) = Reducer.⊕ r (reduce-tree r x) (reduce-tree r y)
reduce-tree r (x ↘ y) = Reducer.⊗ r (reduce-tree r x) (reduce-tree r y)
\end{code}

\subsection{Examples}

\begin{code}
_<<_   : ∀ {A : Set} → A → A → A
a << b = a

_>>_   : ∀ {A : Set} → A → A → A
a >> b = b

label : ∀ {A b} → A → Tree A b → A
label def = reduce-tree (record { ⊕ = _>>_ ; ⊗ = _<<_ ; e = def })

inorder : ∀ {A b} → Tree A b → List A
inorder = reduce-tree (record { ⊕ = _++_ ; ⊗ = _++_ ; e = [] }) ∘ map-tree ([_])

size : ∀ {A b} → Tree A b → ℕ
size = reduce-tree (record { ⊕ = _+_ ; ⊗ = _+_ ; e = 0 }) ∘ map-tree (λ x → 1)

member : ∀ {A b} → A → Tree A b → Bool
member x = reduce-tree (record { ⊕ = _∧_ ; ⊗ = _∧_ ; e = true }) ∘ map-tree {!!}

depth : ∀ {A b} → Tree A b → ℕ
depth = reduce-tree (record { ⊕ = λ a b → suc a ⊔ b ; ⊗ = λ b a → suc a ⊔ b ; e = 0 }) ∘ map-tree (λ x → 1)

heaporder : ∀ {A b} → Tree A b → List A
heaporder = reduce-tree (record { ⊕ = {!!} ; ⊗ = {!!} ; e = [] }) ∘ map-tree ([_])
\end{code}

\section{Accumulations}

\begin{code}
up : ∀ {A b} → Reducer A → A → Tree A b → Tree A b
up r d ⟨⟩ = ⟨⟩
up r d ⟨ a ⟩ = ⟨ a ⟩
up r d (x ↙ ⟨ a ⟩) = up r d x ↙ ⟨ Reducer.⊕ r (label d (up r d x)) a ⟩
up r d (⟨ a ⟩ ↘ y) = ⟨ Reducer.⊗ r a (label d (up r d y)) ⟩ ↘ up r d y
up r d (x ↙ (⟨ a ⟩ ↘ y)) = up r d x ↙ (⟨ Reducer.⊕ r (label d (up r d x)) (Reducer.⊗ r a (label d (up r d y))) ⟩ ↘ up r d y)
up r d ((x ↙ ⟨ a ⟩) ↘ y) = (up r d x ↙ ⟨ Reducer.⊕ r (label d (up r d x)) (Reducer.⊗ r a (label d (up r d y))) ⟩) ↘ up r d y
up r d (x ↙ y) = up r d x ↙ up r d y
up r d (x ↘ y) = up r d x ↘ up r d y

subtrees : ∀ {A b} → A → Tree A true → Tree A b → Tree (Tree A true) b
subtrees d d' = up (record { ⊕ = _↙_ ; ⊗ = _↘_ ; e = ⟨ d ⟩ }) d' ∘ map-tree ⟨_⟩

subtrees-inverse : ∀ {A}{d : A}{d' : Tree A true}{x} → map-tree {b = true} (label d) (subtrees d d' x) ≡ x
subtrees-inverse {x = ⟨ x ⟩} = refl
subtrees-inverse {x = x ↙ y} = {!!}
subtrees-inverse {x = x ↘ y} = {!!}

accum-lemma : ∀ {A}{d : A}{d' : Tree A true}{r}{x} → up {b = true} r d x ≡ (map-tree (reduce-tree r) ∘ subtrees d d') x
accum-lemma {x = ⟨ x ⟩} = refl
accum-lemma {x = x ↙ y} = {!!}
accum-lemma {x = x ↘ y} = {!!}
\end{code}

\section{Building a heap}

\begin{code}
heap : ∀ {A} → (s : List A) → Tree A (null s)
heap = foldl {!!} {!!} ∘ map ⟨_⟩

heap-inverse : ∀ {A}{x} → inorder {A} (heap x) ≡ x
heap-inverse = {!!}
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
