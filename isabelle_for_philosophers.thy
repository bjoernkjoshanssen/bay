(*  Title:      isabelle_for_philosophers.thy
    Author:     Bjørn Kjos-Hanssen
*)


theory isabelle_for_philosophers
  imports Main HOL.Real
begin
(*
Here I reproduce all examples and solve Exercises 1-14 from 
Isabelle for Philosophers by Ben Blumson at https://philarchive.org/archive/BLUIFP
*)

lemma isabelle_for_philosophers_page_2 : "A ⟶ A"
proof (rule impI)
  assume "A"
  then show "A".
qed

lemma positive_paradox : "A ⟶ B ⟶ A"
proof (rule impI)
  assume A
  show "B ⟶ A"
  proof (rule impI)
    assume B
    from ‹A› show A.
  qed
qed

(* Exercise 1:*)
lemma strict_positive_paradox: "A ⟶ B ⟶ B"
proof (rule impI)
  assume A
  show "B ⟶ B"
  proof (rule impI)
    assume B
    thus B. (*thus = then show*)
  qed
qed

lemma modus_ponens : "A ⟶ (A ⟶ B) ⟶ B"
proof (rule impI)
  assume A
  show "(A ⟶ B) ⟶ B"
  proof (rule impI)
    assume "A ⟶ B"
    thus B using ‹A› by (rule mp)
  qed
qed

lemma contraction: "(A ⟶ A ⟶ B) ⟶ (A ⟶ B)"
proof (rule impI)
  assume "A ⟶ A ⟶ B"
  show "A ⟶ B"
  proof (rule impI)
    assume A
    with ‹A ⟶ A ⟶ B› have "A ⟶ B" by (rule mp)
    thus B using ‹A› by (rule mp)
  qed
qed

lemma reverse_contraction : "(A ⟶ A ⟶ B) ⟶ (A ⟶ B)"
proof (rule impI)
  assume "A ⟶ A ⟶ B"
  show "A ⟶ B"
  proof (rule impI)
    assume A
    then have "A ⟶ B" using ‹A ⟶ A ⟶ B› by (rule rev_mp)
    thus B using ‹A› by (rule mp)
  qed
qed

(* Exercise 2 *)
lemma prefixing: "(A ⟶ B) ⟶ (C ⟶ A) ⟶ (C ⟶ B)"
proof (rule impI)
  assume "A ⟶ B"
  show "(C ⟶ A) ⟶ (C ⟶ B)"
  proof (rule impI)
    assume "C ⟶ A"
    show "C ⟶ B"
    proof (rule impI)
      assume "C"
      with ‹C ⟶ A› have "A" by (rule mp)
      with ‹A ⟶ B› have "B" by (rule mp)
      thus "B".
    qed
  qed
qed

lemma suffixing: "(A ⟶ B) ⟶ (B ⟶ C ) ⟶ (A ⟶ C )"
proof (rule impI)
  assume "A ⟶ B"
  show "(B ⟶ C) ⟶ (A ⟶ C)"
  proof (rule impI)
    assume "B ⟶ C"
    show "A ⟶ C"
    proof (rule impI)
      assume "A"
      with ‹A ⟶ B› have "B" by (rule mp)
      with ‹B ⟶ C› have "C" by (rule mp)
      thus "C".
    qed
  qed
qed

lemma "A ⟷ A"
proof (rule iffI)
assume A
thus A.
next
assume A
thus A.
qed

lemma "(A  ⟷ B) ⟶  A ⟶ B"
proof
  assume "A  ⟷ B"
  show "A ⟶ B"
  proof
    assume A
    with ‹A  ⟷ B› show B by (rule iffD1)
  qed
qed

lemma "(A  ⟷ B) ⟶  B ⟶ A"
proof
  assume "A  ⟷ B"
  show "B ⟶ A"
  proof
    assume B
    with ‹A  ⟷ B› show A by (rule iffD2)
  qed
qed

(*Exercise 3*)
lemma "(A ⟷ B) ⟷ (B ⟷ A)"
proof
  assume "(A ⟷ B)"
  show "(B ⟷ A)"
  proof
    assume "B"
    with ‹A  ⟷ B› show A by (rule iffD2)
  next
    assume "A"
    with ‹A  ⟷ B› show B by (rule iffD1)
  qed
  
  next
  assume "(B ⟷ A)"
  show "(A ⟷ B)"
  proof
    assume "A"
    with ‹B  ⟷ A› show B by (rule iffD2)
  next
    assume "B"
    with ‹B  ⟷ A› show A by (rule iffD1)
  qed
qed

lemma "A ∧ B ⟶ A"
proof
assume "A ∧ B"
thus A by (rule conjE)
qed

lemma "A ∧ B ⟶ B"
proof
assume "A ∧ B"
thus B by (rule conjE)
qed

lemma import: "(A ⟶ B ⟶ C) ⟶ (A ∧ B ⟶ C)"
proof
  assume "A ⟶ B ⟶ C"
  show "A ∧ B ⟶ C"
  proof
    assume "A ∧ B"
    then have A by (rule conjE)
    with ‹A ⟶ B ⟶ C› have "B ⟶ C" ..
    from ‹A ∧ B› have B by (rule conjE)
    with ‹B ⟶ C› show C ..
  qed
qed

lemma "A ∧ (A ⟶ B) ⟶ B"
proof
  assume "A ∧ (A ⟶ B)"
  then have "A ⟶ B" by (rule conjE)
  from ‹A ∧ (A ⟶ B)› have A by (rule conjE)
  with ‹A ⟶ B› show B..
qed

lemma strengthening_the_antecedent : "(A ⟶ C ) ⟶ (A ∧ B ⟶ C )"
proof
  assume "(A ⟶ C)"
  show "(A ∧ B ⟶ C)"
  proof
    assume "A ∧ B"
    then have "A"..
    with ‹A ⟶ C› show "C" ..
  qed
qed

lemma conjunction_commutative : "A ∧ B ⟶ B ∧ A"
proof
  assume "A ∧ B"
  hence B..
  from ‹A ∧ B› have A..
  with ‹B› show "B ∧ A" by (rule conjI)
qed

(*Now we finally use named hypotheses:*)
lemma export: "(A ∧ B ⟶ C ) ⟶ (A ⟶ B ⟶ C )"
proof
  assume antecedent: "A ∧ B ⟶ C"
  show "A ⟶ B ⟶ C"
  proof
    assume A
    show "B ⟶ C"
    proof
      assume B
      with ‹A› have "A ∧ B" by (rule conjI)
      with antecedent show C ..
    qed
  qed
qed

lemma conjunction_associative: "A ∧ B ∧ C ⟷ (A ∧ B) ∧ C"
proof
  assume left: "A ∧ B ∧ C"
  hence A..
  from left have "B ∧ C" ..
  hence B..
  with ‹A› have "A ∧ B"..
  from ‹B ∧ C› have C ..
  with ‹A ∧ B› show "(A ∧ B) ∧ C" ..
  next
  assume right: "(A ∧ B) ∧ C"
  hence "A ∧ B"..
  hence "B"..
  from right have C ..
  with ‹B› have "B ∧ C" ..
  from ‹A ∧ B› have A..
  thus "A ∧ B ∧ C" using ‹B ∧ C›..
qed

lemma exercise_5 : "(A ⟶ B) ⟶ (A ⟶ C ) ⟶ A ⟶ B ∧ C"
proof
  assume h0 : "A ⟶ B"
  show "(A ⟶ C ) ⟶ A ⟶ B ∧ C"
  proof
    assume h1 : "A ⟶ C"
    show "A ⟶ B ∧ C"
    proof
      assume h2 : A
      show "B ∧ C"
      proof
        from h0 and h2 show B by (rule mp) (* nice *)
      next
        from h1 and h2 show C by (rule mp)      
      qed
    qed
  qed
qed

lemma "A ⟶ A ∨ B"
proof
assume A
thus "A ∨ B" by (rule disjI1 )
qed

lemma "B ⟶ A ∨ B"
proof
assume B
thus "A ∨ B" by (rule disjI2 )
qed

lemma exercise_6 : "(A ⟶ B) ⟶ (A ⟶ B ∨ C )"
proof
  assume h0 : "A ⟶ B"
  show "A ⟶ B ∨ C"
  proof
    assume h1 : A
    show "B ∨ C"
    proof
      from h0 and h1 show h2 : B by (rule mp) (*I guess a proof of B counts as proof of B ∨ C*)
    qed
  qed
qed

lemma "A ∨ A ⟶ A"
proof
  assume "A ∨ A"
  thus A (* this is mysterious and not explained well. thus we only need to prove A? *)
  proof (rule disjE)
    assume A
    thus A.
    next
    assume A
    thus A.
  qed
qed

lemma "A ∨ A ⟶ A"
proof
  assume "A ∨ A"
  show A
  proof (rule disjE)
    show "A ∨ A" using ‹A ∨ A›. (* just to announce which disjunction we're using*)
    next
    assume A
    thus A.
    next
    assume A
    thus A.
  qed
qed





lemma exercise_7 : "(A ⟶ C ) ∧ (B ⟶ C ) ⟶ A ∨ B ⟶ C"
proof
  assume h : "(A ⟶ C ) ∧ (B ⟶ C )"
  from h have h0 : "A ⟶ C" by (rule conjE)
  from h have h1 : "B ⟶ C" by (rule conjE)
  show " A ∨ B ⟶ C"
  proof
    assume "A ∨ B"
    show "C"
    proof (rule disjE)
        show "A ∨ B" using ‹A ∨ B›. (* just to announce which disjunction we're using*)
        next
          assume A
          thus C using h0 by (simp)

        next
        assume B
        thus C using h1 by (simp)
    qed
  qed
qed

lemma exercise_8 : "A ∨ B ∨ C ⟷ (A ∨ B) ∨ C"
proof
  assume left: "A ∨ B ∨ C"
  show "(A ∨ B) ∨ C"
  proof (rule disjE)
    show "A ∨ B ∨ C" using left.
  next
    assume h : A
    from h have h0 : "A ∨ B" by (rule disjI1)
    from h0 have h1 : "(A ∨ B) ∨ C" by (rule disjI1)
    thus "(A ∨ B) ∨ C".
  next
    assume h2 : "B ∨ C"
    show "(A ∨ B) ∨ C"
    proof (rule disjE)
      show "B ∨ C" using h2.
    next
      assume h3 : "B"
      from h3 have h4 : "A ∨ B" by (rule disjI2)
      from h4 have h5 : "(A ∨ B) ∨ C" by (rule disjI1)
      thus "(A ∨ B) ∨ C".
    next
      assume h3 : "C"
      from h3 have h4 : "(A ∨ B) ∨ C" by (rule disjI2)
      thus "(A ∨ B) ∨ C".
    qed
  qed
next
  assume right: "(A ∨ B) ∨ C"
  show "A ∨ B ∨ C"
  proof (rule disjE)
    show "(A ∨ B) ∨ C" using right.
  next
    assume h : "A ∨ B"
    show "A ∨ (B ∨ C)"
    proof (rule disjE)
      show "A ∨ B" using h.
    next
      assume h0 : "A"
      from h0 have "A ∨ (B ∨ C)" by (rule disjI1)
      thus "A ∨ (B ∨ C)".
    next
      assume h0 : "B"
      from h0 have h1 : "(B ∨ C)" by (rule disjI1)
      from h1 have h2 : "A ∨ (B ∨ C)" by (rule disjI2)
      thus "A ∨ (B ∨ C)".
    qed
  next
    assume h : "C"
    from h have h0 : "B ∨ C"..
    from h0 have h1 : "A ∨ (B ∨ C)"..
    thus "A ∨ (B ∨ C)".
  qed
qed

lemma exercise_9 : "A ∨ B ∧ C ⟶ (A ∨ B) ∧ (A ∨ C )"
proof
  assume h : "A ∨ B ∧ C"
  show  "(A ∨ B) ∧ (A ∨ C )"
  proof (rule disjE)
    show "A ∨ (B ∧ C)" using h.
  next
    assume h0 : "A"
    from h0 have h1 : "A ∨ B" ..
    from h0 have h2 : "A ∨ C" ..
    from h1 and h2 have h3 :  "(A ∨ B) ∧ (A ∨ C )" by (rule conjI)
    thus  "(A ∨ B) ∧ (A ∨ C )".
  next
    assume h0 : "B ∧ C"
    from h0 have h1 : "B" ..
    from h1 have h4 : "A ∨ B" ..

    from h0 have h2 : "C" ..
    from h2 have h5 : "A ∨ C" ..

    with h4 have h3 : "(A ∨ B) ∧ (A ∨ C )" ..
    thus  "(A ∨ B) ∧ (A ∨ C )".
  qed
qed

lemma negative_paradox : "¬ A ⟶ A ⟶ B"
proof
assume "¬ A"
show "A ⟶ B"
  proof
    assume A
    with ‹¬ A› show B by (rule notE)
  qed
qed

(* Exercise 10 *)
lemma explosion: "A ∧ ¬ A ⟶ B"
proof
  assume h : "A ∧ ¬ A"
  from h have h1 : "¬ A" ..
  from h have h0 : A ..
  with h1 show B by (rule notE)
qed

(* Exercise 10 *)
lemma "A ∨ B ⟶ ¬ A ⟶ B"
proof
  assume h : "A ∨ B"
  show  "¬ A ⟶ B"
  proof
    assume h2 : "¬ A"
    show B
    proof (rule disjE)
      show "A ∨ (B)" using h.
    next
      assume h0 : A
      with h2 show B by (rule notE)
    next
      assume h1 : B
      thus B.
    qed
  qed
qed

lemma non_contradiction : "¬ (A ∧ ¬ A)"
proof (rule notI)
  assume h : "A ∧ ¬A"
  hence "¬ A" ..
  moreover from h have A..
  ultimately show False by (rule notE) (*could avoid all this English using from.. have*)
qed

(* Exercise 12 *)
lemma "A ⟶ ¬ ¬ A"
proof
  assume h : A
  show "¬ ¬ A"
  proof (rule notI)
    assume h0 : "¬ A"
    from h0 and h have "False" by (rule notE)
    thus False.
  qed
qed

(* Exercise 13 *)

lemma aux : "¬ (A ∨ ¬ A) ⟶ ¬ A"
proof
  assume h0 : "¬ (A ∨ ¬ A)"
  show "¬ A"
  proof
    assume h1 : A
    then have h2 : "A ∨ ¬ A" ..
    from h0 and h2 have False by (rule notE)
    thus False.
  qed
qed

lemma "¬ ¬ (A ∨ ¬ A)"
proof (rule notI)
  assume h0 : "¬ (A ∨ ¬ A)"
  then have h1 : "¬ A" by (simp) (* should perhaps use lemma aux *)
  then have h2 : "A ∨ ¬ A" ..
  from h0 and h2 have False by (rule notE)
  thus False.
qed

lemma "(¬ A ⟶ False) ⟶ A"
proof
  assume h0 : "¬ A ⟶ False"
  show A
  proof (rule ccontr )
    assume h : "¬ A"
    with h0 show False..
  qed
qed

lemma double_negation_elimination: "¬¬A ⟶ A"
proof
  assume h : "¬¬A"
  show A
  proof (rule ccontr )
    assume "¬ A"
    with h show False..
  qed
qed

(* Exercise 14 *)

lemma excluded_middle: "A ∨ ¬ A"
proof (rule ccontr)
  assume h0 : "¬(A ∨ ¬ A)"
  then have h1 : "¬ A" by (simp) (* should perhaps use lemma aux *)
  then have h2 : "A ∨ ¬ A" ..
  from h0 and h2 have False by (rule notE)
  thus False.
qed

lemma "A ∨ ¬ A"
proof cases
  assume A
  thus "A ∨ ¬ A"..
  next
  assume "¬ A"
  thus "A ∨ ¬ A"..
qed

