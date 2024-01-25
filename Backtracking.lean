import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
import MyProject.exercise_2_2
set_option tactic.hygienic false
set_option maxHeartbeats 3000000


/-
We count the number of words of squarefree words of length L having w as a suffix,
using recursive backtracking. Then we formally prove the correctness.
-/

-- controlled_append:
def capp {n L:ℕ} (b:ℕ) (a:Fin b) (w : Vector (Fin b) (L.succ-n.succ)) (h: ¬ n ≥ L.succ)
                            : Vector (Fin b) (L.succ-n)
:= ⟨ a :: w.1, by {
  rw [List.length_cons]
  simp
  have : n < L.succ := Nat.not_le.mp h
  have : n ≤ L := Nat.not_lt.mp h
  exact (Nat.succ_sub this).symm
}⟩


structure MonoPred (b:ℕ) where
  P : List (Fin b) → Prop
  preserved_under_suffixes : ∀ (u v : List (Fin b)), u <:+ v → P v → P u

def Gap (b:ℕ) (L k : ℕ) : Type := Vector (Fin b) (L - k)
-- A vector of length L monus k, thought of as a possible suffix for a word of length L
-- in which the first k bits are unspecified
-- For example, a Gap 10 10 has length 10 - 10.

-- count_those_with_suffix = number of squarefree words having w as suffix
def count_those_with_suffix {k b :ℕ} {L:ℕ} (M : MonoPred b) [DecidablePred M.P] (w : Gap b L.succ k) : ℕ :=
by {
  induction k
  -- Base case:
  exact ((ite (M.P w.1) 1 0))
  -- Inductive case:
  exact
    (ite (M.P w.1))
    (
      dite (n ≥ L.succ)
      (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ List.sum (
          List.map (λ a ↦ (n_ih (capp b a w h))) (List.ofFn id) -- this much does not rely on it being Fin 2
        )
      )
    )
    0
}

def those_with_suffix {k b :ℕ} {L:ℕ} (M : MonoPred b) [DecidablePred M.P] (w : Gap b L.succ k) : Finset (Vector (Fin b) L.succ) :=
by {
  induction k
  -- Base case:
  exact ((ite (M.P w.1) {w} ∅))
  -- Inductive case:
  exact
    (ite (M.P w.1))
    (
      dite (n ≥ L.succ)
      (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
          (λ a ↦ (n_ih (capp b a w h)))
        )
      )
    )
    ∅
}


theorem extsf (b:ℕ) (u v : List (Fin b))
(h: u <:+ v) (hu : squarefree v) : squarefree u := by {
  unfold squarefree; unfold squarefree at hu; intro lx; intro; intro x hx
  rcases h with ⟨t,ht⟩; intro hc
  have hgood: (x.1 ++ x.1).length ≤ u.length :=  List.IsInfix.length_le hc
  rcases hc with ⟨s₀,hs₀⟩; rcases hs₀ with ⟨s₁,hs₁⟩
  have : lx < v.length := calc
        lx  = x.1.length := x.2.symm
        _   < x.1.length + x.1.length := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   = (x.1 ++ x.1).length := (List.length_append x.1 x.1).symm
        _   ≤ u.length := hgood
        _   ≤ t.length + u.length := by linarith
        _   = v.length := by {rw [← List.length_append t u,ht]}
  let G := hu lx this x hx; unfold List.IsInfix at G
  have : ∃ s t, s ++ (x.1 ++ x.1) ++ t = v := by {exists t ++ s₀; exists s₁; rw [← ht,← hs₁]; simp}
  exact G this
}

theorem extsf3 (b:ℕ) (u v : List (Fin b))
(h: u <:+ v) (hu : cubefree v) : cubefree u := by {
  unfold cubefree; unfold cubefree at hu; intro lx; intro; intro x hx
  rcases h with ⟨t,ht⟩; intro hc
  have hgood: (x.1 ++ x.1 ++ x.1).length ≤ u.length :=  List.IsInfix.length_le hc
  rcases hc with ⟨s₀,hs₀⟩; rcases hs₀ with ⟨s₁,hs₁⟩
  have : lx < v.length := calc
        lx  = x.1.length := x.2.symm
        _   < x.1.length + x.1.length := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   ≤ x.1.length + x.1.length + x.1.length := Nat.le_add_right (List.length x.1 + List.length x.1) (List.length x.1)
        _   = (x.1 ++ x.1).length + x.1.length := by rw[(List.length_append x.1 x.1).symm]
        _   = (x.1 ++ x.1 ++ x.1).length := by exact (List.length_append (x.1 ++ x.1) x.1).symm
        _   ≤ u.length := hgood
        _   ≤ t.length + u.length := by linarith
        _   = v.length := by {rw [← List.length_append t u,ht]}
  let G := hu lx this x hx; unfold List.IsInfix at G
  have : ∃ s t, s ++ (x.1 ++ x.1 ++ x.1) ++ t = v := by {exists t ++ s₀; exists s₁; rw [← ht,← hs₁]; simp}
  exact G this
}

def SQF (b:ℕ) : MonoPred b := {
  P := (λ w : List (Fin b) ↦ squarefree w)
  preserved_under_suffixes := extsf b
}

def CBF (b:ℕ): MonoPred b := {
  P := (λ w : List (Fin b) ↦ cubefree w)
  preserved_under_suffixes := extsf3 b
}

instance (b:ℕ): DecidablePred ((SQF b).P) := by {
  unfold SQF
  simp
  exact inferInstance
}

instance  (b:ℕ): DecidablePred ((CBF b).P) := by {
  unfold CBF
  simp
  exact inferInstance
}


-- def myvec : Vector (Fin 2) (3-1) := ⟨[0,1],rfl⟩

def myvec10 := (⟨[],rfl⟩ : Gap 2 10 10)
def myvec9  : Gap 2 9 9   := ⟨[],rfl⟩
def myvec8  : Gap 2 8 8   := ⟨[],rfl⟩
def myvec7  : Gap 2 7 7   := ⟨[],rfl⟩
def myvec := (⟨[],rfl⟩ : Gap 3 8 8)

#eval count_those_with_suffix (CBF 2) myvec9
#eval those_with_suffix (CBF 2) myvec9


#eval those_with_suffix (SQF 3) myvec

-- #eval count_those_with_suffix CBF myvec8
-- #eval count_those_with_suffix CBF myvec7
-- example : count_those_with_suffix SQF myvec10 = 0 := by decide

-- #eval count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 10 10) -- 118 cubefree words of length 10
-- but producing a proof takes longer:
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 4 4) = 10 := by decide
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 5 5) = 16 := by decide
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 6 6) = 24 := by decide
--The number of binary cubefree words of length
-- n=1, 2, 3,  4,  5,  6,  7,  8,  9,  10, ... are
--   2, 4, 6, 10, 16, 24, 36, 56, 80, 118, ... (OEIS A028445)

theorem cons_suffix (b:ℕ)
{L n_1: ℕ} {a : Fin b}
(h: ¬n_1 ≥ Nat.succ L)
(w: Vector (Fin b) (Nat.succ L -  (Nat.succ n_1)))

: w.1 <:+ (capp b a w h).1 := by {
  exists [a];
}

theorem branch_out (b:ℕ) {n L:ℕ} (M:MonoPred b)[DecidablePred M.P] (h: ¬ n ≥ L.succ) (w : Vector (Fin b) (L.succ-n.succ)) :
  count_those_with_suffix M (w)
  = List.sum (List.map (λ a ↦ count_those_with_suffix M (capp b a w h)) (List.ofFn id))
  := by {
    induction n
    -- Base step:
    unfold count_those_with_suffix
    simp
    intro H

    -- BLOCK
    have h₀₁: ∀ a, ¬ M.P (capp b a w h).1 :=
      by {intro a hc; exact H (M.preserved_under_suffixes w.1 (capp b a w h).1 (cons_suffix b _ _) hc)}
    symm
    have : List.ofFn (fun a => if MonoPred.P M (capp b a w (by linarith)).1 then (1:ℕ) else (0:ℕ))
     = List.replicate b 0 := by {
      refine List.eq_replicate.mpr ?_
      constructor
      simp
      intro i hi
      simp at hi
      rw [List.mem_iff_get] at hi
      rcases hi with ⟨n,hn⟩
      simp at hn
      rw [if_neg (h₀₁ _)] at hn
      exact hn.symm
    }
    rw [this]
    apply List.sum_const_nat b 0
    -- END OF BLOCK

    -- Inductive step:
    unfold count_those_with_suffix
    simp
    by_cases H : (M.P w.1)
    rw [if_pos H,dif_neg h]

    rw [if_neg H]
    -- BLOCK
    have h₀₁: ∀ a, ¬ M.P (capp b a w h).1 :=
      by {intro a hc; exact H (M.preserved_under_suffixes w.1 (capp b a w h).1 (cons_suffix b _ _) hc)}

    -- Jan.24: here we need, if all ite are false then the sum is zero
    --rw [if_neg (h₀₁ 0),if_neg (h₀₁ 1)]
    symm
    have : (List.ofFn fun a =>
      if MonoPred.P M (capp b a w h).1 then
        if h : Nat.succ L ≤ n_1 then
          Nat.rec (motive := fun {k} => Gap b (Nat.succ L) k → ℕ) (fun w => if MonoPred.P M w.1 then 1 else 0)
            (fun n n_ih w =>
              if MonoPred.P M w.1 then
                if h : Nat.succ L ≤ n then n_ih { val := [], property := (by {
                  simp
                  exact (Nat.sub_eq_zero_of_le h).symm
                } : List.length [] = Nat.succ L - n) }
                else List.sum (List.ofFn fun a => n_ih (capp b a w (h : ¬n ≥ Nat.succ L)))
              else 0)
            n_1 { val := [], property := ((by simp;exact (Nat.sub_eq_zero_of_le h).symm) : List.length [] = Nat.succ L - n_1) }
        else
          List.sum
            (List.ofFn fun a_1 =>
              Nat.rec (motive := fun {k} => Gap b (Nat.succ L) k → ℕ) (fun w => if MonoPred.P M w.1 then 1 else 0)
                (fun n n_ih w =>
                  if MonoPred.P M w.1 then
                    if h : Nat.succ L ≤ n then n_ih { val := [], property := ((by simp;exact
                      (Nat.sub_eq_zero_of_le h).symm) : List.length [] = Nat.succ L - n) }
                    else List.sum (List.ofFn fun a => n_ih (capp b a w (h : ¬n ≥ Nat.succ L)))
                  else 0)
                n_1 (capp b a_1 (capp b a w (by {
                  rename_i hh
                  exact hh
                })) (h : ¬n_1 ≥ Nat.succ L)))
      else 0)
     = List.replicate b 0 := by {
      refine List.eq_replicate.mpr ?_
      constructor
      simp
      intro i hi
      simp at hi
      rw [List.mem_iff_get] at hi
      rcases hi with ⟨n,hn⟩
      simp at hn
      rw [if_neg (h₀₁ _)] at hn
      exact hn.symm
    }
    rw [this]
    apply List.sum_const_nat b 0
    -- END OF BLOCK
  }



theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
 {x : α // P x} =  {x : α // Q x} := by {
  have : ∀ x, P x = Q x := fun x => propext (h x)
  have : P = Q := funext this
  exact congrArg Subtype this
}

theorem fincard_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x) [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
  Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by {
  have H: {x // P x} = {x // Q x} := subtype_ext P Q h
  simp_rw [H]
}

theorem disjoint_branch  {L : ℕ}
{M:MonoPred 2} [DecidablePred M.P]
  -- {n:ℕ}
  -- (w: Vector (Fin 2) (L.succ-n.succ))
  -- (h : ¬ n ≥ L.succ)
  :
  Disjoint (λ v  : Vector (Fin 2) L.succ ↦ M.P v.1 ∧ (capp 2 0 w h).1 <:+ v.1 )
           (λ v  : Vector (Fin 2) L.succ ↦ M.P v.1 ∧ (capp 2 1 w h).1 <:+ v.1 ) :=
  by {
      unfold Disjoint
      intro S h0S h1S v hSv
      exfalso
      rcases (h0S v hSv).2 with ⟨t₀,ht₀⟩
      rcases (h1S v hSv).2 with ⟨t₁,ht₁⟩
      rw [← ht₀] at ht₁
      unfold capp at ht₁
      simp at ht₁

      have : t₁ ++ [1] ++ w.1 = t₀ ++ [0] ++ w.1:= calc
                            _ = t₁ ++ 1 :: w.1 := (List.append_cons t₁ 1 w.1).symm
                            _ = t₀ ++ 0 :: w.1 := ht₁
                            _ = _ := (List.append_cons t₀ 0 w.1)

      have : t₁ ++ [1] = t₀ ++ [0] := (List.append_left_inj w.1).mp this
      have : (t₁ ++ [1]).getLast (by simp) = (t₀ ++ [0]).getLast (by simp) :=
        List.getLast_congr _ _ this
      simp at this
    }


-- We formally verify only for b=2.
theorem formal_verification_of_recursive_backtracking (k L:ℕ) (bound : k ≤ L.succ) (M:MonoPred 2) [DecidablePred M.P]
(w : Vector (Fin 2) (L.succ-k)):
  Fintype.card {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1}
  = count_those_with_suffix M w
:= by {
  induction k
  have h₁: ∀ v : Vector (Fin 2) L.succ, w.1 <:+ v.1 → w.1 = v.1 := by {
    intro v hv; exact List.eq_of_suffix_of_length_eq hv (by {rw [v.2,w.2];simp})
  }
  have h₂: ∀ x y : {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1}, x = y := by {
    intro x y
    let Gx := h₁ x x.2.2
    let Gy := h₁ y y.2.2
    exact SetCoe.ext (SetCoe.ext (Eq.trans Gx.symm Gy))
  }
  unfold count_those_with_suffix
  simp
  by_cases hs : (M.P w.1)
  rw [if_pos hs]
  let u : {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1} := ⟨w,⟨hs, List.suffix_rfl⟩⟩
  let G := subsingleton_iff.mpr (h₂)
  let H := uniqueOfSubsingleton u
  refine Fintype.card_unique
  rw [if_neg hs]
  have : ∀ v: Vector (Fin 2) L.succ ,¬ (M.P v.1 ∧ w.1 <:+ v.1) := by {
    intro v hc
    have : v = w := (SetCoe.ext (h₁ v hc.2)).symm
    subst this
    exact hs hc.1
  }
  let K := Subtype.isEmpty_of_false this
  exact Fintype.card_eq_zero
  -- Induction step:
  by_cases h : (n ≥ L.succ)
  exfalso
  have : L.succ < L.succ := calc
              _ ≤ n := h
              _ < n.succ := Nat.lt.base n
              _ ≤ L.succ := bound
  exact LT.lt.false this

  let g₀ := capp 2 0 w h --(0 ::ᵥ w)
  let g₁ := capp 2 1 w h

  have halt: ∀ v : Vector (Fin 2) L.succ, M.P v.1 ∧ w.1 <:+ v.1 ↔
    (M.P v.1 ∧ g₀.1 <:+ v.1) ∨ (M.P v.1 ∧ g₁.1 <:+ v.1)  := by {
    intro v; constructor; intro h
    rcases h.2 with ⟨t,ht⟩
    have hlong: t ≠ List.nil := by {
      intro hc; rw [hc] at ht; simp at ht; have : w.1.length = v.1.length := congr_arg _ ht
      rw [w.2,v.2] at this; contrapose this; simp; intro hL
      have : L.succ ≤ L := calc
                  _ = L - n := hL.symm
                  _ ≤ L := Nat.sub_le L n
      cases (Nat.lt_or_eq_of_le this); contrapose h_1; linarith; contrapose h_1; exact Nat.succ_ne_self L
    }
    have : t.reverse ≠ List.nil := by {
      intro hc; have : t.reverse.reverse = [].reverse := congrArg List.reverse hc
      simp at this; exact hlong this
    }
    rcases (List.exists_cons_of_ne_nil this) with ⟨a,ha⟩
    rcases ha with ⟨s,hs⟩
    have hsr : t.reverse.reverse = (a :: s).reverse := congrArg List.reverse hs
    have hr: t = s.reverse ++ [a] := by {simp at hsr; rw [hsr]}
    by_cases ha: (a=0)
    left; constructor; exact h.1; exists s.reverse; rw [← ht]; rw [hr]; subst ha; simp; rfl

    have ha: a = 1 := Fin.eq_one_of_neq_zero a ha
    right; constructor; exact h.1; exists s.reverse; rw [← ht]; rw [hr]; subst ha; simp; rfl

    intro hi; cases hi
    constructor; exact h_1.1; rcases h_1.2 with ⟨u,hu⟩; exists u ++ [0]; rw [← hu]; simp; rfl
    constructor; exact h_1.1; rcases h_1.2 with ⟨u,hu⟩; exists u ++ [1]; rw [← hu]; simp; rfl
  }

  have hcard: Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1 }
       = Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ g₀.1 <:+ v.1 }
       + Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ g₁.1 <:+ v.1 }
    := by {rw [fincard_ext _ _ halt,← Fintype.card_subtype_or_disjoint _ _ disjoint_branch]}

  rw [hcard,branch_out,n_ih (Nat.le_of_lt bound) g₀,n_ih (Nat.le_of_lt bound) g₁]
  simp
  exact h
}
