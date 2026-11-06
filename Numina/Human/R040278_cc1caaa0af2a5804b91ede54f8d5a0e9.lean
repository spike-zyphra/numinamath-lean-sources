import Mathlib

/- 1. If the set of real numbers
  $$
  A=\{2 x, 3 y\} \text { and } B=\{6, x y\}
  $$

  have exactly one common element, then the product of all elements in $A \cup B$ is $\qquad$ . -/
theorem algebra_301808 (x y : ℝ):
    let A : Finset ℝ := {2 * x, 3 * y}
    let B : Finset ℝ := {6, x * y};
    2 * x ≠ 3 * y → 6 ≠ x * y →
    (∃ a , A ∩ B = {a}) →
    ∏ x ∈ A ∪ B, x = 0 :=
by
  rintro A B neq1 neq2 ⟨a, ah⟩
  -- This is a lemma we will use.
  have insert_eq (x a : ℝ) (A : Finset ℝ): insert x A = {a} → a = x := by
    intro h
    have : x ∈ ({a} : Finset ℝ) := by
      rewrite [←h]
      exact Finset.mem_insert_self x A
    simp at this
    symm
    assumption
  -- Case on `a` being `0` or not.
  rcases em (a = 0) with (h|h)
  . -- Case `a = 0`
    -- This is possible.
    subst h
    have : 0 ∈ A ∪ B := by
      have : ∀ a ∈ A ∩ B , a ∈ A :=  fun a a_1 ↦ Finset.mem_of_mem_filter a a_1
      have : 0 ∈ A := by
        apply this
        rewrite [ah]
        simp
      apply Finset.mem_union_left
      assumption
    have : ∀ (A : Finset ℝ), 0 ∈ A → ∏ x ∈ A, x = 0 := fun A a ↦ Finset.prod_eq_zero a rfl
    apply this
    assumption
  . -- Case `a ≠ 0`
    -- This is not possible. We will show that.
    exfalso
    -- Now we cases on each equality between two sets.
    rcases em (x = 0) with (h1|h1)
    . subst x;
      rcases em (y = 0) with (h2|h2)
      . subst y
        simp [A, B] at ah
        apply h; symm; assumption
      . simp [A, B] at ah
        have : a = 0 := by
          apply insert_eq
          exact ah
        apply h
        assumption
    . rcases em (y = 0) with (h2|h2)
      . subst h2
        simp [A, B] at ah
        have : ({2 * x, 0} ∩ {6, 0} : Finset ℝ) = {0, 2*x} ∩ {0, 6} := by
          rewrite [Finset.pair_comm, Finset.pair_comm 6 0]
          simp
        rw [this] at ah
        simp at ah
        apply h
        apply insert_eq
        exact ah
      . rcases em (x = 3) with (h3|h3)
        . subst h3
          simp [A,B, show (2 * 3 : ℝ) = 6 by ring_nf] at ah
          apply_fun Finset.card at ah
          simp [*] at ah
        . rcases em (y = 2) with (h4|h4)
          . subst h4
            simp [A, B] at ah
            rewrite [show (3 * 2 : ℝ) = 6 by ring_nf, Finset.pair_comm, mul_comm] at ah
            apply_fun Finset.card at ah
            simp [*] at ah
          . -- This is the final case.
            -- We will show that `A ∩ B` is empty.
            have H1 : 2 * x ≠ 6 ∧ 2 * x ≠ x * y := by
              constructor
              . apply_fun (fun x : ℝ => x / 2)
                ring_nf
                assumption
              . apply_fun (fun x' : ℝ => x' / x)
                ring_nf
                have : x * x ⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel x h1
                rewrite [this]
                ring_nf
                tauto
            have H2 : 3 * y ≠ 6 ∧ 3 * y ≠ x * y := by
              constructor
              . apply_fun (fun x : ℝ => x / 3)
                ring_nf
                assumption
              . apply_fun (fun x : ℝ => x / y)
                ring_nf
                have : y * y ⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel y h2
                rewrite [this]
                ring_nf
                tauto
            have s1 : B ∩ {2 * x, 3 * y} = B ∩ {3 * y} := by
              apply Finset.inter_insert_of_not_mem
              simp [B]
              tauto
            have s2 : B ∩ {3 * y} = B ∩ ∅ := by
              apply Finset.inter_insert_of_not_mem (s₂ := ∅)
              simp [B]
              tauto
            have : A ∩ B = ∅ := by
              rewrite [Finset.inter_comm]
              simp [A]
              trans
              . exact s1
              . trans
                . exact s2
                . simp
            rewrite [this] at ah
            apply_fun Finset.card at ah
            simp [*] at ah
