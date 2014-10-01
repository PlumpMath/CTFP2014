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

open import Level using () renaming (zero to lzero)
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.List as L
open import Data.Vec as V
open import Function
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary.Core
\end{code}
%endif

\section{Trees}

\begin{code}
data Tree (A : Set) : Bool × Bool → Set where
  ⟨⟩  : Tree A (false , false)
  ⟨_⟩ : A → Tree A (true , true)
  _↙_ : ∀ {lx rx ry} → Tree A (lx , rx) → Tree A (true , ry) → Tree A (false , ry)
  _↘_ : ∀ {lx ly ry} → Tree A (lx , true) → Tree A (ly , ry) → Tree A (lx , false)
\end{code}

\section{Maps and reduces}

\begin{code}
map-tree : ∀ {A B lr} → (A → B) → Tree A lr → Tree B lr
map-tree f ⟨⟩ = ⟨⟩
map-tree f ⟨ x ⟩ = ⟨ f x ⟩
map-tree f (x ↙ y) = map-tree f x ↙ map-tree f y
map-tree f (x ↘ y) = map-tree f x ↘ map-tree f y

record Reducer A : Set where
  field
    ⊕ : A → A → A
    ⊗ : A → A → A
    e : A

reduce-tree : ∀ {A lr} → Reducer A → Tree A lr → A
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

label : ∀ {A lr} → A → Tree A lr → A
label def = reduce-tree (record { ⊕ = _>>_ ; ⊗ = _<<_ ; e = def })

inorder : ∀ {A lr} → Tree A lr → List A
inorder = reduce-tree (record { ⊕ = L._++_ ; ⊗ = L._++_ ; e = [] }) ∘ map-tree (L.[_])

size : ∀ {A lr} → Tree A lr → ℕ
size = reduce-tree (record { ⊕ = _+_ ; ⊗ = _+_ ; e = 0 }) ∘ map-tree (λ x → 1)

member : ∀ {A lr} → A → Tree A lr → Bool
member x = reduce-tree (record { ⊕ = _∧_ ; ⊗ = _∧_ ; e = true }) ∘ map-tree {!!}

depth : ∀ {A lr} → Tree A lr → ℕ
depth = reduce-tree (record { ⊕ = λ a b → suc a ⊔ b ; ⊗ = λ b a → suc a ⊔ b ; e = 0 }) ∘ map-tree (λ x → 1)

heaporder : ∀ {A lr} → Tree A lr → List A
heaporder = reduce-tree (record { ⊕ = {!!} ; ⊗ = {!!} ; e = [] }) ∘ map-tree (L.[_])
\end{code}

\section{Accumulations}

\begin{code}
up : ∀ {A lr} → Reducer A → A → Tree A lr → Tree A lr
up r d ⟨⟩ = ⟨⟩
up r d ⟨ a ⟩ = ⟨ a ⟩
up r d (x ↙ ⟨ a ⟩) = up r d x ↙ ⟨ Reducer.⊕ r (label d (up r d x)) a ⟩
up r d (x ↙ (⟨ a ⟩ ↘ y)) = up r d x ↙ (⟨ Reducer.⊕ r (label d (up r d x)) (Reducer.⊗ r a (label d (up r d y))) ⟩ ↘ up r d y)
up r d (⟨ a ⟩ ↘ y) = ⟨ Reducer.⊗ r a (label d (up r d y)) ⟩ ↘ up r d y
up r d ((x ↙ ⟨ a ⟩) ↘ y) = up r d x ↙ (⟨ Reducer.⊕ r (label d (up r d x)) (Reducer.⊗ r a (label d (up r d y))) ⟩ ↘ up r d y)

-- subtrees : ∀ {A lr} → A → Tree A ? {!!} → Tree A ? ? → Tree (Tree A {!!} ?) ? ?
-- subtrees d d' = up (record { ⊕ = _↙_ ; ⊗ = _↘_ ; e = ⟨ d ⟩ }) d' ∘ map-tree ⟨_⟩

--subtrees-inverse : ∀ {A}{d : A}{d' : Tree A ?}{x} → map-tree {b = ?} (label d) (subtrees d d' x) ≡ x
--subtrees-inverse {x = ⟨ x ⟩} = refl
--subtrees-inverse {x = x ↙ y} = {!!}
--subtrees-inverse {x = x ↘ y} = {!!}

--accum-lemma : ∀ {A}{d : A}{d' : Tree A ?}{r}{x} → up {b = ?} r d x ≡ (map-tree (reduce-tree r) ∘ subtrees d d') x
--accum-lemma {x = ⟨ x ⟩} = refl
--accum-lemma {x = x ↙ y} = {!!}
--accum-lemma {x = x ↘ y} = {!!}
\end{code}

\section{Building a heap}

\begin{code}
module HeapOrder {ℓ₁ ℓ₂}{ord : DecTotalOrder Level.zero ℓ₁ ℓ₂} where
  open DecTotalOrder ord renaming (_≤_ to _⊑_; _≤?_ to _⊑?_; Carrier to A)

  -- doesn't termination check because the checker doesn't see associativity well
  -- playing with parentheses placement puts termination errors into different places
  _⊕h'_ : ∀ {xx yy} → Tree A xx → Tree A yy → Σ (Bool × Bool) (λ zz → Tree A zz)
  -- identities
  _⊕h'_ {false , false} {yy} ⟨⟩ y  = yy , y
  _⊕h'_ {xx} {false , false} x ⟨⟩  = xx , x

  -- juicy meat
  ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v) with a ⊑? b
  ... | yes p                         = ((false , false) , (x ↙ ⟨ a ⟩) ↘ proj₂ (y ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)))
  ... | no ¬p                         = ((false , false) , proj₂ (((x ↙ ⟨ a ⟩) ↘ y) ⊕h' u) ↙ (⟨ b ⟩ ↘ v))
  ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' (u ↙ (⟨ b ⟩ ↘ v)) with a ⊑? b
  ... | yes p                         = ((false , false) , (x ↙ ⟨ a ⟩) ↘ proj₂ (y ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)))
  ... | no ¬p                         = ((false , false) , proj₂ (((x ↙ ⟨ a ⟩) ↘ y) ⊕h' u) ↙ (⟨ b ⟩ ↘ v))
  (x ↙ (⟨ a ⟩ ↘ y)) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v) with a ⊑? b
  ... | yes p                         = ((false , false) , (x ↙ ⟨ a ⟩) ↘ proj₂ (y ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)))
  ... | no ¬p                         = ((false , false) , proj₂ (((x ↙ ⟨ a ⟩) ↘ y) ⊕h' u) ↙ (⟨ b ⟩ ↘ v))
  (x ↙ (⟨ a ⟩ ↘ y)) ⊕h' (u ↙ (⟨ b ⟩ ↘ v)) with a ⊑? b
  ... | yes p                         = ((false , false) , (x ↙ ⟨ a ⟩) ↘ proj₂ (y ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)))
  ... | no ¬p                         = ((false , false) , proj₂ (((x ↙ ⟨ a ⟩) ↘ y) ⊕h' u) ↙ (⟨ b ⟩ ↘ v))

  -- boring cruft
  ⟨ a ⟩             ⊕h' ⟨ b ⟩             = ((⟨⟩ ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ ⟨⟩)
  ⟨ a ⟩             ⊕h' (u ↙ ⟨ b ⟩)       = ((⟨⟩ ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ ⟨⟩)
  ⟨ a ⟩             ⊕h' (u ↙ (⟨ b ⟩ ↘ v)) = ((⟨⟩ ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)
  ⟨ a ⟩             ⊕h' (⟨ b ⟩ ↘ v)       = ((⟨⟩ ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ v)
  ⟨ a ⟩             ⊕h' ((u ↙ ⟨ b ⟩) ↘ v) = ((⟨⟩ ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)

  (x ↙ ⟨ a ⟩)       ⊕h' ⟨ b ⟩             = ((x ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (x ↙ ⟨ a ⟩)       ⊕h' (u ↙ ⟨ b ⟩)       = ((x ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (x ↙ ⟨ a ⟩)       ⊕h' (⟨ b ⟩ ↘ v)       = ((x ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ v)
  (x ↙ ⟨ a ⟩)       ⊕h' (u ↙ (⟨ b ⟩ ↘ v)) = ((x ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)
  (x ↙ ⟨ a ⟩)       ⊕h' ((u ↙ ⟨ b ⟩) ↘ v) = ((x ↙ ⟨ a ⟩) ↘ ⟨⟩) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)
  
  (⟨ a ⟩ ↘ y)       ⊕h' ⟨ b ⟩             = ((⟨⟩ ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (⟨ a ⟩ ↘ y)       ⊕h' (⟨ b ⟩ ↘ v)       = ((⟨⟩ ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ v)
  (⟨ a ⟩ ↘ y)       ⊕h' (u ↙ ⟨ b ⟩)       = ((⟨⟩ ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (⟨ a ⟩ ↘ y)       ⊕h' (u ↙ (⟨ b ⟩ ↘ v)) = ((⟨⟩ ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)
  (⟨ a ⟩ ↘ y)       ⊕h' ((u ↙ ⟨ b ⟩) ↘ v) = ((⟨⟩ ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ v)

  ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ⟨ b ⟩       = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (x ↙ (⟨ a ⟩ ↘ y)) ⊕h' ⟨ b ⟩       = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ ⟨⟩)
  ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' (u ↙ ⟨ b ⟩) = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ ⟨⟩)
  ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' (⟨ b ⟩ ↘ v) = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ v)
  (x ↙ (⟨ a ⟩ ↘ y)) ⊕h' (u ↙ ⟨ b ⟩) = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((u ↙ ⟨ b ⟩) ↘ ⟨⟩)
  (x ↙ (⟨ a ⟩ ↘ y)) ⊕h' (⟨ b ⟩ ↘ v) = ((x ↙ ⟨ a ⟩) ↘ y) ⊕h' ((⟨⟩ ↙ ⟨ b ⟩) ↘ v)

  HTree : Set → Set
  HTree A = Σ (Bool × Bool) (λ zz → Tree A zz)

  _⊕h_ : HTree A → HTree A → HTree A
  (proj₁ , proj₂) ⊕h (proj₃ , proj₄) = proj₂ ⊕h' proj₄

  heap : ∀ {n} → (s : Vec A (suc n)) → HTree A
  heap = V.foldl₁ _⊕h_ ∘ V.map (λ x → (true , true) , ⟨ x ⟩)

  heap-inverse : ∀ {n}{x : Vec A (suc n)} → inorder {A} (proj₂ (heap x)) ≡ toList x
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
