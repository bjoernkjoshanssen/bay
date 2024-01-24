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
def capp {n L:ℕ} (a:Fin 2) (w : Vector (Fin 2) (L.succ-n.succ)) (h: ¬ n ≥ L.succ)
                            : Vector (Fin 2) (L.succ-n)
:= ⟨ a :: w.1, by {
  rw [List.length_cons]
  simp
  have : n < L.succ := Nat.not_le.mp h
  have : n ≤ L := Nat.not_lt.mp h
  exact (Nat.succ_sub this).symm
}⟩


structure MonoPred where
  P : List (Fin 2) → Prop
  preserved_under_suffixes : ∀ (u v : List (Fin 2)), u <:+ v → P v → P u

-- count_those_with_suffix = number of squarefree words having w as suffix
def count_those_with_suffix {k L:ℕ} (M : MonoPred) [DecidablePred M.P] (w : Vector (Fin 2) (L.succ-k)) : ℕ :=
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
      (λ h ↦ (n_ih (capp 0 w h))
          +  (n_ih (capp 1 w h)))
    )
    0
}

theorem extsf (u v : List (Fin 2))
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

def SQF : MonoPred := {
  P := (λ w : List (Fin 2) ↦ squarefree w)
  preserved_under_suffixes := extsf
}

instance : DecidablePred (SQF.P) := by {
  unfold SQF
  simp
  exact inferInstance
}

def myvec : Vector (Fin 2) (3-1) := ⟨[0,1],rfl⟩
#eval count_those_with_suffix SQF myvec
-- This shows there is one squarefree word over {0,1} of length 3 with suffix 01, namely 101.
example : count_those_with_suffix SQF myvec = 1 := by decide

theorem cons_suffix
{L n_1: ℕ} {a : Fin 2}
(h: ¬n_1 ≥ Nat.succ L)
(w: Vector (Fin 2) (Nat.succ L -  (Nat.succ n_1)))

: w.1 <:+ (capp a w h).1 := by {
  exists [a];
}

theorem branch_out {n L:ℕ} (M:MonoPred)[DecidablePred M.P] (h: ¬ n ≥ L.succ) (w : Vector (Fin 2) (L.succ-n.succ)) :
  count_those_with_suffix M (w)
  = count_those_with_suffix M (capp 0 w h)
  + count_those_with_suffix M (capp 1 w h)
  := by {
    induction n
    -- Base step:
    unfold count_those_with_suffix
    simp
    intro H
    -- BLOCK
    have h₀: ¬ M.P (capp 0 w h).1 := by {intro hc; exact H (M.preserved_under_suffixes w.1 (capp 0 w h).1 (cons_suffix _ _) hc)}
    have h₁: ¬ M.P (capp 1 w h).1 := by {intro hc; exact H (M.preserved_under_suffixes w.1 (capp 1 w h).1 (cons_suffix _ _) hc)}
    rw [if_neg h₀,if_neg h₁]
    -- END OF BLOCK

    -- Inductive step:
    unfold count_those_with_suffix
    simp
    by_cases H : (M.P w.1)
    rw [if_pos H,dif_neg h]

    rw [if_neg H]
    -- BLOCK
    have h₀: ¬ M.P (capp 0 w h).1 := by {intro hc; exact H (M.preserved_under_suffixes w.1 (capp 0 w h).1 (cons_suffix _ _) hc)}
    have h₁: ¬ M.P (capp 1 w h).1 := by {intro hc; exact H (M.preserved_under_suffixes w.1 (capp 1 w h).1 (cons_suffix _ _) hc)}
    rw [if_neg h₀,if_neg h₁]
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

theorem disjoint_branch {L : ℕ} {M:MonoPred} [DecidablePred M.P]:
  Disjoint (λ v  : Vector (Fin 2) L.succ ↦ M.P v.1 ∧ (capp 0 w h).1 <:+ v.1 )
           (λ v  : Vector (Fin 2) L.succ ↦ M.P v.1 ∧ (capp 1 w h).1 <:+ v.1 ) :=
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


theorem formal_verification_of_recursive_backtracking (k L:ℕ) (bound : k ≤ L.succ) (M:MonoPred) [DecidablePred M.P]
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

  let g₀ := capp 0 w h --(0 ::ᵥ w)
  let g₁ := capp 1 w h

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

}
