(*  Title:      isabelle_for_philosophers.thy
    Author:     Bjørn Kjos-Hanssen
*)


theory isabelle_for_philosophers
  imports Main HOL.Real
begin
(*
Here I reproduce all examples and solve all the exercises (1 -- 34) from 
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

lemma excluded_middle': "¬ A ∨ A"
proof (rule ccontr)
  assume h0 : "¬(¬ A ∨ A)"
  then have h1 : "¬ A" by (simp) (* should perhaps use lemma aux *)
  then have h2 : " ¬ A ∨ A" ..
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

lemma exercise_15 : "(A ⟶ B) ∨ (A ⟶ ¬ B)"
proof cases
  assume h : B
  then have h0 : "A ⟶ B" ..
  then have h1 : "(A ⟶ B) ∨ (A ⟶ ¬ B)" ..
  thus "(A ⟶ B) ∨ (A ⟶ ¬ B)".
next
  assume h : "¬ B"
  then have h0 : "(A ⟶ ¬ B)" ..
  then have h1 : "(A ⟶ B) ∨ (A ⟶ ¬ B)" ..
  thus "(A ⟶ B) ∨ (A ⟶ ¬ B)".
qed

lemma exercise_16 : "(A ⟶ B) ∨ (B ⟶ A)" 
proof cases
  assume h : B
  then have h0 : "A ⟶ B" ..
  then have h1 : "(A ⟶ B) ∨ (B ⟶ A)" ..
  thus "(A ⟶ B) ∨ (B ⟶ A)".
next
  assume h : "¬ B"
  then have "(B ⟶ A)" by (simp)
  then have  "(A ⟶ B) ∨ (B ⟶ A)" ..
  thus  "(A ⟶ B) ∨ (B ⟶ A)" .
qed

lemma exercise_17 : "(A ∨ B) ∧ (A ∨ C ) --> A ∨ B ∧ C"
proof
  assume h : "(A ∨ B) ∧ (A ∨ C )"
  show " A ∨ (B ∧ C)"
  proof cases
    assume h0 : A
    then have  " A ∨ (B ∧ C)" ..
    thus  " A ∨ (B ∧ C)".
  next
    assume h0 : "¬ A"
    from h have h1 : "A ∨ B" ..
    with h0 have h2 : B by (simp)
    from h have h3 : "A ∨ C" ..
    with h0 have h4 : C by (simp)
    from h2 and h4 have h5 : "B ∧ C" ..
    thus "A ∨ (B ∧ C)" ..
  qed
qed

lemma exercise_18_i : "(A ⟶ B) ⟷ (¬ A ∨ B)"
proof
  assume h : "(A ⟶ B)"
  show " (¬ A ∨ B)"
  proof cases
    assume h0 : A
    with h have B ..
    thus "¬ A ∨ B" ..
  next
    assume h0 : "¬ A"
    thus "¬ A ∨ B" ..
  qed    
next
  assume h :  " (¬ A ∨ B)"
  show "(A ⟶ B)"
  proof
    assume h0 : "A"
    show "B"
    proof (rule disjE)
      show " (¬ A ∨ B)" using h.
      next
      assume h1 : "¬ A"
      from h1 and h0 have B by (rule notE)
      thus B.
    next
      assume "B"
      thus "B".
    qed
  qed
qed


lemma exercise_18_ii : "(A ⟶ B) ⟷ ¬ (A ∧ ¬ B)"
proof
  assume h : "(A ⟶ B)"
  show "¬ (A ∧ ¬ B)"
  proof
    assume h0 : "A ∧ ¬ B"
    from h0 have h1 : A ..
    with h have h3 : B ..
    from h0 have h2 : "¬ B" ..
    from h2 and h3 have False ..
    thus False.
  qed
next
  assume h :  "¬ (A ∧ ¬ B)"
  show "(A ⟶ B)"
  proof
    assume h0 : "A"
    show "B"
    proof (rule ccontr)
      assume h1 : "¬ B"
      with h0 have h2 : "A ∧ ¬ B" ..
      with h have False ..
      thus False.
    qed
  qed
qed


(* Exercise 19 *)
lemma
assumes h0 : "A ∨ ¬ A"
assumes h1 : "A ⟶ B ⟶ A"
assumes h2 : "(B ⟶ A) ⟶ D"
assumes h3 : "¬ A ⟶ C ⟶ ¬ A"
assumes h4 : "(C ⟶ ¬ A) ⟶ D"
shows D
proof (rule disjE)
  show "(A ∨ ¬ A)" using h0.
next
  assume h1 : "A"
  from h1 have "B ⟶ A" ..
  with h2 have D ..
  thus D.
next
  assume h5 : "¬ A"
  from h5 have "C ⟶ ¬ A" ..
  with h4 have D ..
  thus D.
qed

(* Now, quantifiers: *)

lemma "(∀ x . F x ) ⟶ F a"
proof
assume "∀ x . F x"
thus "F a" by (rule allE)
qed

lemma exercise_20 : "(∀ x . F x ) ⟶ F a ∧ F b"
proof
assume h : "∀ x . F x"
  from h have ha : "F a" by (rule allE)
  from h have hb : "F b" by (rule allE)
  from ha and hb have h0 : "F a ∧ F b" ..
  thus  "F a ∧ F b".
qed

lemma exercise_21 : "(∀ x . R x d) ⟶ (∀ z . R d z ⟶ z = m) ⟶ d = m"
proof
  assume h0 : "(∀ x . R x d)"
  show "(∀ z . R d z ⟶ z = m) ⟶ d = m"
  proof
    assume h1 : "(∀ z . R d z ⟶ z = m)"
    from h0 have h2 : "R d d" ..
    from h1 have h3 : "R d d ⟶ d = m" ..
    from h3 and h2 have "d = m" ..
    thus "d = m".
  qed
qed

lemma "∀ x . F x ⟶ F x" (* . in Isabelle is like . in Lean *)
proof (rule allI)
  fix a
  show "F a ⟶ F a"
  proof
  assume "F a"
  thus "F a".
  qed
qed

lemma exercise_22 : "(∀ x . F x ∧ G x ) ⟶ (∀ x . F x )"
proof
  assume h : "(∀ x . F x ∧ G x )"
  show " (∀ x . F x )"
  proof
    fix a
    from h have h0 : "F a ∧ G a" ..
    from h0 have "F a" ..
    thus "F a".
  qed
qed

(* This one is just wrong. *)
lemma exercise_23 : "(∀ x . F x ) ⟶ (∀ x . F x ⟶ G x )" nitpick oops
(* This is probably what was meant: *)

lemma exercise_23' : "(∀ x . F x ) ⟶ (∀ x . G x ⟶ F x )"
proof
  assume h : "(∀ x . F x )"
  show "(∀ x . G x ⟶ F x)"
  proof
    fix a
    show "G a ⟶ F a"
    proof
      assume "G a"
      from h have "F a" ..
      thus "F a".
    qed
  qed
qed

lemma "F a ⟶ (∃ x . F x )"
proof
assume "F a"
thus "∃ x . F x" by (rule exI)
qed

lemma "∃ x. x = x"
  by force

lemma "∃ x . F x ∨ ¬ F x"
proof (-)
  from excluded_middle have h : "F a ∨ ¬ F a". (* Using the lemma excluded_middle above *)
    thus  "∃ x . F x ∨ ¬ F x" by (rule exI)
  qed

(*
This example doesn't follow from excluded_middle as stated, because the ¬ is on the left vs. on the right.
*)
lemma as_stated : "∃ x . ¬ F x ∨ F x" 
proof (-)
  from excluded_middle' have h : "¬ F a ∨ F a". (* Using the lemma excluded_middle above *)
    thus  "∃ x .  ¬ F x ∨ F x" by (rule exI)
  qed

lemma exercise_24 : " (∃ x . (∃ y. F y) ⟶ F x)"
proof (rule disjE)
  show "(∃ y . F y) ∨ (¬ (∃ y . F y))" using excluded_middle. (* very finicky about parentheses *)
next
  assume "∃ y . F y"
  then obtain a where "F a" by (rule exE)
  hence h : "(∃ y . F y) ⟶ F a" ..
  thus  "∃ x . (∃ y. F y) ⟶ F x" ..
next
  assume "(¬ (∃ y . F y))"
  then have h : " (∃ y. F y) ⟶ F a" by (simp)
  from h have  "∃ x . (∃ y. F y) ⟶ F x" by (rule exI)
  thus  "∃ x . (∃ y. F y) ⟶ F x".
qed


lemma ex_25_helper :  "¬ (∃ x . ¬ F x) ⟶ (∀ x . F x)"
proof
  assume h : "¬ (∃ x . ¬ F x)"
  show "∀ x . F x"
  proof
    fix a
    show "F a"
    proof (rule ccontr)
        assume hc : "¬ F a"
        then have h0 : "∃ x . ¬ F x" ..
        from h and h0 have "False" by (rule notE)
        thus "False".
    qed
  qed
qed

(* Exercise 25 *)
lemma not_all_implies_some_not: "¬ (∀ x . F x ) ⟶ (∃ x . ¬ F x )"
proof
  assume h0 : "¬ (∀ x . F x )"
  show " (∃ x . ¬ F x )"
  proof (rule ccontr)
    assume "¬ (∃ x . ¬ F x )"
    with ex_25_helper have h1 : "∀ x . F x" ..
    from h0 and h1 have False by (rule notE)
    thus False.
  qed
qed

lemma exercise_26 : "(∀ x . F x ) ⟶ (∃ x . F x )"
proof
  assume "∀ x . F x"
  then have "F a" ..
  thus "∃ x . F x" ..
qed

(* Existential elimination: *)
lemma "(∃ x . F x ∧ G x ) ⟶ (∃ x . F x )"
proof
  assume "∃ x . F x ∧ G x"
  then obtain a where "F a ∧ G a" by (rule exE)
  hence "F a" ..
  thus "∃ x . F x" ..
qed

lemma exercise_27 : "(∃ x . F x ) ⟶ (∃ x . F x ∨ G x )"
proof
  assume h : "(∃ x . F x )"
  from h obtain a where ha : "F a" by (rule exE)  
  then have h0 : "F a ∨ G a" ..
  
  from h0 have h1 : "∃ x . F x ∨ G x" ..
  thus "∃ x . F x ∨ G x".
qed

lemma exercise_28 : "∃ x . F x ⟶ (∀ x . F x )"
proof (rule disjE)
  show "(∀ x . F x) ∨ (¬ (∀ x . F x))" using excluded_middle.
next
  assume h : "(∀ x . F x)"
  from h have "F a ⟶ (∀ x . F x)" ..
  thus  "∃ x . F x ⟶ (∀ x . F x )" ..
next
  assume h : " (¬ (∀ x . F x))"
  with not_all_implies_some_not have h0 : "∃ x . ¬ F x" ..
  from h0 obtain a where h1: "¬ F a" by (rule exE)
  from h1 have h2 : "F a ⟶ (∀ x . F x)" by (simp)
  from h2 have h3 :  "∃ x . F x ⟶ (∀ x . F x )" ..
  thus  "∃ x . F x ⟶ (∀ x . F x )".
qed

lemma "∀ x . x = x"
proof
  fix a
  show "a = a" by (rule refl)
qed

lemma exercise_29 : "F a ⟶ a = a" 
proof
  assume "F a"
  show "a = a" by (rule refl)
qed

lemma exercise_30 : "∀ x . ∃ y. x = y"
proof
  fix a
  have h : "a = a" by (rule refl)
  from h have h0 : "∃ y . a = y" ..
  show  "∃ y . a = y" using h0.
qed

lemma "a = b ⟶ F a ⟶ F b"
proof
  assume h : "a = b"
  show "F a ⟶ F b"
  proof
    assume "F a"
    with h show "F b" by (rule subst)
  qed
qed

lemma substitution : "a = b ⟶ F b ⟶ F a"
proof
  assume h : "a = b"
  show "F b ⟶ F a"
  proof
    assume "F b"
    with h show "F a" by (rule ssubst)
  qed
qed

lemma exercise_31 : "a = b ⟶ b = a"
proof
  assume h : "a = b"
  from h have "b = a" ..
  thus "b = a".
qed

lemma exercise_32 : "a = b ⟶ b = c ⟶ a = c"
proof
  assume h : "a = b"
  show "(b = c) ⟶ (a = c)"
  proof
    assume "b = c"
    with h show "a = c" by (rule ssubst)
  qed
qed

lemma exercise_33 : "x = y ⟶ (F x ⟷ F y)"
proof
  assume h : "x = y"
  show "F x ⟷ F y"
  proof
    assume h0 : "F x"
    with h show "F y" by (rule subst)
  next
    assume h0 : "F y"
    with h show "F x" by (rule ssubst)
  qed
qed

lemma "(THE x . x = a) = a"
proof (rule the_equality)
  show "a = a" ..
  next
  fix b
  assume "b = a"
  thus "b = a".
qed

lemma "(∀ x . F x ) ⟶ F (THE x . G x )"
proof
assume "∀ x . F x"
thus "F (THE x . G x )" by (rule allE)
qed

lemma exercise_34 : "(∀ x . F x ⟷ x = a) ⟶ (THE x . F x ) = a"
proof
  assume h : "(∀ x . F x ⟷ x = a)"
  show "(THE x . F x ) = a"
  proof (rule the_equality)

    from h have h0 : "F a ⟷ a = a" ..
    from h0 have h1 : "a = a ⟶ F a" ..
    have h2 : "a = a" by (rule refl)
    from h1 and h2 have "F a" ..
    thus "F a".
  next
    fix b
    assume h3 : "F b"
    from h have h4 : "F b ⟷ b = a" ..
    from h4 have h5 : "F b ⟶ b = a" ..
    from h5 and h3 have h6 : "b = a" by (rule mp)
    thus "b = a".
  qed
qed

lemma
  assumes "p ⟶ q"
  assumes q
  shows p nitpick oops
  
lemma "(∀ x . F x ⟶ G x ) ∨ (∃ x . F x ∧ ¬ G x )" sledgehammer
  by auto  

lemma "(∀ x . F x ⟶ G x ) ∨ (∃ x . F x ∧ ¬ G x )" sledgehammer [isar_proofs]
proof -
{ assume "¬ F v0_0 ∨ G v0_0"
have ?thesis
by blast }
  then show ?thesis
    by blast
qed

lemma "(∀ x . ∃ y. R x y) ⟶ (∃ y. ∀ x . R x y)" try oops
lemma "(∃ x . ∀ y. R x y) ⟶ (∀ y. ∃ x . R x y)" try
by auto
