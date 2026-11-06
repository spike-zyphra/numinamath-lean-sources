import Mathlib

/- 5. Let $S=\{1,2, \cdots, 500\}$, choose any 4 different numbers from $S$, and arrange them in ascending order to form a geometric sequence with a positive integer ratio. Find the number of such geometric sequences. -/
theorem number_theory_111419 :
    let S: Finset ℤ := Finset.Icc 1 500
    Set.ncard {a : Fin 4 → ℤ | ∃ x y z w : ℤ, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ w ∈ S ∧
      a = ![x, y, z, w] ∧ x < y ∧ y < z ∧ z < w ∧
      ∃ r : ℤ, r > 0 ∧ y = x * r ∧ z = y * r ∧ w = z * r} = 94 := by

  intro S

  -- we will change the set, which cardinaliity we have to prove,
  -- into something nicer, using this lemma
  have H (a: Fin 4 → ℤ):
      (∃ x y z w, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ w ∈ S ∧
      a = ![x, y, z, w] ∧ x < y ∧ y < z ∧ z < w ∧
      ∃ (r: ℤ), 0 < r ∧ y = x * r ∧ z = y * r ∧ w = z * r) ↔
      (∃ r t, a = ![t, t * r, t * r ^ 2, t * r ^ 3] ∧
      2 ≤ r ∧ r ≤ 7 ∧ 1 ≤ t ∧ t * r ^ 3 ≤ 500) := by

    unfold S at *
    constructor <;> intro H

    . -- let's destruct the big statement `H` into its parts
      obtain ⟨x, y, z, w, Hx, Hy, Hz, Hw, H, H0, H1, H2, r, H3, H4, H5, H6⟩ := H
      -- also we replace variables `y`, `z` and `w` everywhere
      -- with their expressions (hypotheses `H4`, `H5` and `H6`)
      subst y z w
      -- then we use variables `r` and `t` as witnesses for the goal
      use r, x
      -- let's simplify everywhere -
      -- to replace these `Finset.Icc` with inequalities
      simp at *
      -- we will prove all the five parts of the goal separately
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      . -- `H` is the same as goal after simplifying it with `ring_nf`
        ring_nf at H
        exact H
      . -- two cases: `r = 1` or `2 ≤ r`, both simple to prove
        have H7: r = 1 ∨ 2 ≤ r := by omega
        obtain H7 | H7 := H7
        . subst r
          simp at *
        . exact H7
      . -- if statement `r ≤ 7` is false or, in other words, `8 ≤ r`,
        -- then the expression `x * r ^ 3` is too big
        -- and we get contradiction
        by_contra H7
        have H8: 512 ≤ x * r * r * r := by nlinarith
        omega
      . exact Hx.1
      . ring_nf at Hw
        exact Hw.2

    . -- let's destruct the big statement `H` into its parts
      obtain ⟨r, t, Ha, H0, H1, H2, H3⟩ := H
      -- we use the values `t`, `t * r`, `t * r ^ 2`, `t * r ^ 3`
      -- as witness for the goal
      use t, t * r, t * r ^ 2, t * r ^ 3
      -- let's simplify the goal to replace `Finset.Icc`
      -- with inequalities everywhere
      simp
      -- now we divide the goal into nine parts
      -- and prove each separately,
      -- (lot's of `linarith` used)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      . constructor
        . exact H2
        . have H4: 1 ≤ r ^ 3 := by nlinarith
          nlinarith
      . constructor
        . nlinarith
        . nlinarith
      . constructor
        . nlinarith
        . nlinarith
      . constructor
        . have H4: 1 ≤ r ^ 3 := by nlinarith
          nlinarith
        . exact H3
      . exact Ha
      . nlinarith
      . have H4: r < r ^ 2 := by nlinarith
        nlinarith
      . have H4: r ^ 2< r ^ 3 := by nlinarith
        nlinarith
      . -- in this last part of the goal we use `r`
        -- as witness for the goal,
        -- then prove remaining goal parts separately
        use r
        refine ⟨?_, ?_, ?_, ?_⟩
        . linarith
        . tauto
        . ring
        . ring

  -- let's replace the set in the goal using `H`
  -- also we remove hypotheses `H` and `S`,
  -- because we will not need them anymore
  simp_rw [H]; clear H S

  -- transform the set into nested indexed union of sets
  rw [Set.setOf_exists]
  simp_rw [Set.setOf_exists]

  -- let's replace the set with better equivalent set
  -- which is simpler for calculating its cardinality
  have H0:
      ⋃ (r: ℤ), ⋃ (t: ℤ), {x | x = ![t, t * r, t * r ^ 2, t * r ^ 3] ∧ 2 ≤ r ∧ r ≤ 7 ∧ 1 ≤ t ∧ t * r ^ 3 ≤ 500} =
      ⋃ r ∈ Finset.Icc 2 7, ⋃ t ∈ Finset.Icc 1 (500 / (r ^ 3)), {x | x = ![t, t * r, t * r ^ 2, t * r ^ 3]} := by

    -- we use set extensionality again
    ext w; simp at *

    constructor <;> intro H1
    . obtain ⟨r, t, H1, H2, H3, H4, H5⟩ := H1
      use r, t
      refine ⟨?_, ?_, ?_, ?_⟩
      . have H6: 0 < r := by linarith
        have H7: 0 < r ^ 3 := Lean.Omega.Int.pos_pow_of_pos r 3 H6
        exact (Int.le_ediv_iff_mul_le H7).mpr H5
      . exact ⟨H2, H3⟩
      . exact H4
      . exact H1
    . obtain ⟨r, t, H1, H2, H3, H4⟩ := H1
      use r, t
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      . exact H4
      . exact H2.1
      . exact H2.2
      . exact H3
      . have H5: 0 < r := by linarith
        have H6: 0 < r ^ 3 := Lean.Omega.Int.pos_pow_of_pos r 3 H5
        exact (Int.le_ediv_iff_mul_le H6).mp H1

  -- replace in the goal using lemma we just proved
  rw [H0]; clear H0

  -- we need to prove that these sets are pairwise disjoint
  -- for different values in the interval `Finset.Icc 2 7`
  have H0: Set.PairwiseDisjoint (Finset.Icc (2: ℤ) 7)
            (fun (r: ℤ) => (Finset.Icc 1 (500 / r ^ 3)).biUnion
               fun x_1 => {![x_1, x_1 * r, x_1 * r ^ 2, x_1 * r ^ 3]}) := by
    intros i Hi j Hj Hne
    intros H1 H2 H3
    simp at *
    ext x
    simp
    intro H4
    -- we will prove that `False`
    have H5 := H2 H4
    have H6 := H3 H4
    simp at *
    obtain ⟨a, H7, H8⟩ := H5
    obtain ⟨b, H9, H10⟩ := H6
    -- it follows that `![a, a * i, a * i ^ 2, a * i ^ 3] = ![b, b * i, b * i ^ 2, b * i ^ 3]`,
    -- therefore `a = b` (the first value in both finite lists)
    rw [H8] at H10
    rw [funext_iff] at H10
    have H11 := H10 0
    simp at H11
    -- from that it follows that `i = j` too, which gives as contradiction
    -- because also `i ≠ j`
    have H12 := H10 1
    simp at H12
    subst a
    have H13: i = j := by nlinarith
    tauto

  -- and here too: for each integer `r` we prove pairwise disjointness
  have H1 (r: ℤ): Set.PairwiseDisjoint (Finset.Icc 1 (500 / r ^ 3))
      (fun (t: ℤ) => ({![t, t * r, t * r ^ 2, t * r ^ 3]}: Finset (Fin 4 → ℤ))) := by
    intros i Hi j Hj Hne
    intros w H2 H3
    simp
    ext x
    simp at H2 H3 ⊢
    intro H5
    -- after all introductions and simplifications
    -- we have two statements made from disjunctions in the hypotheses.
    -- let's destuct them and prove all goals we get
    obtain H2 | H2 := H2
    . subst w
      simp at H5
    . obtain H3 | H3 := H3
      . rw [H3] at H5
        simp at H5
      . rw [H2] at H3
        simp at H3
        rw [funext_iff] at H3
        have H4 := H3 0
        simp at H4
        tauto

  -- rewrites to get `biUnion` in the goal instead of `iUnion`
  simp_rw [Set.setOf_eq_eq_singleton, ← Finset.mem_coe, ← Finset.coe_singleton,
    ← Finset.coe_biUnion, Set.ncard_coe_Finset]

  -- now we use `conv` mode - to replace places of the goal
  -- with better equal values
  conv =>
    rw [Finset.card_biUnion H0]
    enter [1, 2, r]
    rw [Finset.card_biUnion (H1 r)]
    enter [2, t]
    simp

  -- now there is a simple calculation left to finish the proof
  rfl