import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
import MyProject.BacktrackingVerification
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

-- Before we can erase extend_fold
-- we must address the fact that
-- those_with_suffix uses predicates on Lists not Vectors.
-- But that's a problem because then the type of P and Q become part of the induction
-- in a new way.
-- so the predicate P should say about a list and a "phobe" something about them both restricted
-- to the minimum of their lengths.


-- Encoding the allowed moves for the rectangular lattice structure on ℤ × ℤ using Fin 4:
def move_fin : Fin 4 →ℤ×ℤ → ℤ×ℤ
| 0 => (. + ( 1,  0))
| 1 => (. + (-1,  0))
| 2 => (. + ( 0,  1))
| 3 => (. + ( 0, -1))

theorem finfin {l : ℕ} {k: Fin l} (i : Fin k): i.1 < l := calc
  _ < k.1 := i.isLt
  _ < l   := k.isLt

def F : Bool → ℕ := λ b ↦ ite (b=true) 1 0

/- Start of unused, other lattice structures. -/

def move_fin₃ : Fin 6 → (ℤ×ℤ×ℤ → ℤ×ℤ×ℤ)
| 0 => (. + ( 1, 0, 0))
| 1 => (. + (-1, 0, 0))
| 2 => (. + ( 0, 1, 0))
| 3 => (. + ( 0,-1, 0))
| 4 => (. + ( 0, 0, 1))
| 5 => (. + ( 0, 0,-1))

def pp : ℤ×ℤ → ℤ×ℤ := (. + ( 1, 1))
def ps : ℤ×ℤ → ℤ×ℤ := (. + ( 1, 0))
def sp : ℤ×ℤ → ℤ×ℤ := (. + ( 0, 1))

def mm : ℤ×ℤ → ℤ×ℤ := (. + (-1,-1))
def ms : ℤ×ℤ → ℤ×ℤ := (. + (-1, 0))
def sm : ℤ×ℤ → ℤ×ℤ := (. + ( 0,-1))

def pm : ℤ×ℤ → ℤ×ℤ := (. + ( 1,-1))
def mp : ℤ×ℤ → ℤ×ℤ := (. + (-1, 1))


-- move_hex represents the degree-6 hexagonal/triangular lattice, although that in itself requires checking
def move_hex : Fin 6 →ℤ×ℤ → ℤ×ℤ
| 0 => ps
| 1 => ms
| 2 => λ x ↦ ite (Even x.2) (sp x) (pp x)
| 3 => λ x ↦ ite (Even x.2) (mm x) (sm x)
| 4 => λ x ↦ ite (Even x.2) (mp x) (sp x)
| 5 => λ x ↦ ite (Even x.2) (sm x) (pm x)
#eval move_hex 0 (0,0)
#eval move_hex 5 (1,0)

-- move_tri represents the degree-3 hexagonal/triangular lattice, although that in itself requires checking
def move_tri : Fin 3 → ℤ×ℤ → ℤ×ℤ
| 0 => ps
| 1 => λ x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)
| 2 => ms



/- End of unused, other lattice structures. -/


def nearby_with  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]
[∀ i v w, Decidable (go i v = w)]
(p q : α) : Bool :=
∃ a : Fin b, q = go a p


def point_achieved_with  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)] {l : ℕ}
  (fold : Vector (α) l) (a b : Fin l) (phobic : Vector Bool l) : Bool
:= by {
  exact phobic.get a && phobic.get b && a.1.succ < b.1 && nearby_with go (fold.get a) (fold.get b)
}

def pts_at_with_modern {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ}
(k : Fin l) (ph : Vector Bool l)
  (fold : Vector α l) :=
  List.sum (
    List.map F (
      List.ofFn (λ i : Fin k ↦ point_achieved_with (go : Fin b → α → α) fold ⟨i.1,finfin _⟩ k ph)
    )
  )

def points_modern{α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ} (ph : Vector Bool l)
  (fold : Vector α l) := List.sum (List.ofFn (λ i : Fin l ↦ pts_at_with_modern go i ph (fold)))


/- The use of OfNat here is a clever(?) way of indicating that all folds should start at the origin,
and we only try to do protein folding in lattices that have a natural notion of base point or zero.
-/
def walk' {α:Type} [OfNat α 0]  {b : ℕ} (go : Fin b → α → α)
  (l : List (Fin b)) :  {l : List α // l ≠ List.nil} := by {
  induction l
  . exact ⟨[0], List.cons_ne_nil _ _⟩
  . exact ⟨(go head (List.head tail_ih.1 tail_ih.2)) :: tail_ih.1, List.cons_ne_nil _ _⟩
}

def walk {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
(l : List (Fin b)) : List α :=
  (walk' go l.reverse).1






theorem moves_len'
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α) (l : List (Fin b)) :
  (walk' go l).1.length = l.length.succ := by {
  induction l
  . unfold walk'; rw [List.length_cons]; rfl
  . unfold walk'; simp; rw [← Nat.succ_eq_add_one,← tail_ih]; unfold walk'; simp
}

theorem moves_len
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α) (l : List (Fin b)) :
  (walk go l).length = l.length.succ := by {
    unfold walk; rw [moves_len']; simp
}

def first_nonzero_entry (w : List (Fin 4)) : Option (Fin 4) := by {
  induction w
  .  exact none
  .  exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)
}

-- By symmetry we may assume that all walks (folds) are orderly, although that in itself could deserve a proof.
def orderly (w: List (Fin 4)) := w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2

instance (w : List (Fin 4)) : Decidable (orderly w) := by unfold orderly; exact And.decidable


def stecher (x : List Bool) (w: List (Fin 4)) : ℕ :=
  dite (w.length.succ = x.length)
    (λ h ↦ points_modern
      move_fin
      (⟨x, rfl⟩ : Vector Bool x.length) -- no longer reverse somehow
      (⟨walk move_fin w,by {rw [moves_len move_fin w]; tauto}⟩ : Vector (ℤ×ℤ) x.length)
    )
    (λ _ ↦ 0)

def x : List Bool := [true,false,true,false,true,false, true,true]
#eval stecher x [0, 3, 1, 1, 2, 2, 0]
-- #eval stecher (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse

def stecher1 : Prop :=
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (walk move_fin w).get i))
    (λ w ↦ stecher x w > 2 ∧ orderly w)
    (Gap_nil' 4 7)
  = {⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval (myvec 4 7).length
-- #eval stecher1

def stecher2 : Prop :=
those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (walk move_fin w).get i))
    (
      λ w ↦ stecher (x ++ [false]) w > 2
        ∧ orderly w
    )
    (Gap_nil' 4 8) = ∅

def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2


instance : Decidable stecher2 := by unfold stecher2; apply decEq
instance : Decidable stecher_conjecture_counterexample := by {
  unfold stecher_conjecture_counterexample
  unfold stecher1
  unfold stecher2
  exact And.decidable
}

-- #eval stecher2
#eval stecher_conjecture_counterexample
