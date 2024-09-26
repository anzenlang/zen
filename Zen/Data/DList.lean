import Zen.Init

/-! # Dependent lists -/
namespace Zen

/-- Implementation detail for `DList`: dependent list type with reversed arguments.

We want `DList n α`, but doing so makes `α : Type u` a parameter of the constructors, causing to
jump a universe and thus `DList n α : Type u + 1` which is bad.
-/
inductive DList.DList' (α : Type u) : (n : Nat) → Type u
| nil : DList' α 0
| cons (head : α) (tail : DList' α n) : DList' α n.succ

/-- Dependent lists of length `n` storing `α`-elements.

This type is realized by `DList.DList'`, so make sure to use `.nil` and `.cons` when
pattern-matching `DList`-values. Constructors are re-exported under `DList`: `DList.nil` and
`DList.cons`.
-/
def DList (n : Nat) (α : Type u) : Type u :=
  DList.DList' α n

namespace DList

/-! ## Constructors and basic functions -/

/-- The empty list. -/
def nil : DList 0 α :=
  DList'.nil

/-- Builds a `DList (n + 1)` from a `DList n`. -/
def cons (head : α) (tail : DList n α) : DList n.succ α :=
  DList'.cons head tail

/-- The length of a list. -/
abbrev length (_ : DList n α) : Nat := n

@[inherit_doc length]
abbrev len := @length

/-- Legal index for a list `dl`, allows writing `dl.Idx`. -/
abbrev Idx (_ : DList n α) : Type := Fin n

/-- Builds a list that repeats a value `n` times. -/
def many (a : α) (n : Nat) : DList n α :=
  aux .nil n (by simp)
where
  aux : {i : Nat} → (acc : DList i α) → (j : Nat) → (h : i + j = n) → DList n α
  | _, acc, 0, h => h ▸ acc
  | _, acc, j + 1, h =>
    aux (acc.cons a) j (by omega)

/-- Builds a list that repeats a default value `n` times. -/
def manyD [Inhabited α] (n : Nat) : DList n α :=
  many default n

@[inherit_doc many]
def gen (a : α) : DList n α := many a n

@[inherit_doc manyD]
def genD [Inhabited α] : DList n α := manyD n

/-- Reverses a list. -/
def reverse (self : DList n α) : DList n α :=
  aux .nil self (by simp)
where
  aux {i j : Nat} : (acc : DList i α) → (dl : DList j α) → (h : i + j = n) → DList n α
  | acc, .nil, h => h.symm ▸ acc
  | acc, .cons hd tl, h =>
    aux (acc.cons hd) tl (by omega)

/-! ## `map` -/

/-- Monadic map, gives access to indices. -/
def mapIdxM [Monad m]
  (self : DList n α)
  (f : self.Idx → α → m β)
: m (DList n β) :=
  aux (by simp) self
where
  aux : {i : Nat} → (h : i ≤ n) → DList i α → m (DList i β)
  | 0, _, .nil => return .nil
  | i + 1, h, .cons hd tl => do
    let idx : self.Idx :=
      ⟨n - (i + 1), Nat.sub_lt_of_pos_le (by simp) h⟩
    let hd ← f idx hd
    let tl : DList i β ← aux (by exact Nat.le_of_succ_le h) tl
    return tl.cons hd

/-- Monadic map. -/
def mapM [Monad m] (self : DList n α) (f : α → m β) : m (DList n β) :=
  self.mapIdxM (𝕂 f)

/-- Map, gives access to indices. -/
def mapIdx (self : DList n α) (f : self.Idx → α → β) : DList n β :=
  self.mapIdxM (m := Id) (return f · ·)

/-- Map over lists. -/
protected def map (self : DList n α) (f : α → β) : DList n β :=
  self.mapM (m := Id) (return f ·)

instance : Functor (DList n) where
  map f self := self.map f

@[inherit_doc many]
protected abbrev pure (a : α) : DList n α :=
  many a n

instance : Pure (DList n) := ⟨DList.pure⟩

/-! ## `fold` -/

/-- Monadic fold-left, gives access to indices. -/
def foldlIdxM [Monad m]
  (self : DList n α)
  (init : β)
  (f : β → self.Idx → α → m β)
: m β :=
  aux (by simp) init self
where
  aux : {i : Nat} → (h : i ≤ n) → (acc : β) → DList i α → m β
  | 0, _, acc, .nil => return acc
  | i + 1, h, acc, .cons hd tl => do
    let idx : self.Idx :=
      ⟨n - (i + 1), Nat.sub_lt_of_pos_le (by simp) h⟩
    let acc ← f acc idx hd
    aux (Nat.le_of_succ_le h) acc tl

/-- Monadic fold-left. -/
def foldlM [Monad m] (self : DList n α) (init : β) (f : β → α → m β) : m β :=
  self.foldlIdxM init fun b _ => f b

/-- Fold-left, gives access to indices. -/
def foldlIdx (self : DList n α) (init : β) (f : β → self.Idx → α → β) : β :=
  self.foldlIdxM (m := Id) init f

/-- Fold-left over lists. -/
def foldl (self : DList n α) (init : β) (f : β → α → β) : β :=
  self.foldlM (m := Id) init f

/-! ## Element retrieval -/

/-- Retrieves an element. -/
def get {n : Nat} : (self : DList n α) → (idx : self.Idx) → α
| .cons hd _, ⟨0, _⟩ => hd
| .cons _ tl, ⟨i + 1, h_i⟩ => tl.get ⟨i, by omega⟩

/-- Retrieves an element if the index is legal. -/
def get? (self : DList n α) (idx : Nat) : Option α :=
  if h : idx < n then self.get ⟨idx, h⟩ else none

/-- Retrieves an element if the index is legal, crashes otherwise. -/
def get! [Inhabited α] (self : DList n α) (idx : Nat) : α :=
  if let some elm := self.get? idx
  then elm
  else panic! s!"illegal index `{idx}` for d-list of length `{n}`"

instance : GetElem? (DList n α) Nat α (fun _ idx => idx < n) where
  getElem self idx h := self.get ⟨idx, h⟩
  getElem? := get?
