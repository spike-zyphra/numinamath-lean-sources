import Mathlib

theorem algebra_16715 (S : Set ℝ) (hS : S = {f 1 | (f : ℝ → ℝ) (_ : ∀ x y, f ((x - y) ^ 2) = f x ^ 2 - 2 * x * f y + y ^ 2)}) :
  Set.ncard S * ∑ᶠ x ∈ S, x = 6 := by
  have h1 : S = {1, 2} := by
    rw [hS]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Show that if x ∈ S, then x = 1 or x = 2
      intro hx
      rcases hx with ⟨f, hf, rfl⟩

      have h_eq1 : ∀ x, (f x - x) ^ 2 = f 0 := by
        intro x
        specialize hf x x
        simp at hf
        nlinarith

      have h_eq2 : f 0 = 0 ∨ f 0 = 1 := by
        have h0 : (f 0 - (0 : ℝ)) ^ 2 = f 0 := by
          specialize h_eq1 0
          simpa using h_eq1
        have : (f 0) ^ 2 - f 0 = 0 := by nlinarith
        have : f 0 * (f 0 - 1) = 0 := by nlinarith
        cases (mul_eq_zero.mp this) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith

      cases h_eq2 with
      | inl h00 =>
        have h_eq3 : ∀ x, f x = x := by
          intro x
          have h : (f x - x) ^ 2 = (0 : ℝ) := by
            rw [h_eq1 x, h00]
            all_goals norm_num
          have : f x - x = 0 := by nlinarith
          linarith

        left
        exact h_eq3 1

      | inr h01 =>
        have h_eq3 : ∀ x, (f x - x) ^ 2 = 1 := by
          intro x
          specialize h_eq1 x
          rw [h01] at h_eq1
          nlinarith

        have h_eq4 : f 1 = 2 := by
          have h1 : (f 1 - (1 : ℝ)) ^ 2 = 1 := by
            apply h_eq3 1
          have h2 := hf 1 0
          simp [show f 0 = 1 by linarith] at h2
          nlinarith [h1, h2, h_eq3 1]

        right
        linarith

    · -- Show that if x = 1 or x = 2, then x ∈ S
      rintro (rfl | rfl)
      · -- Prove 1 is in S
        use (fun x => x)
        use (by
          intro x y
          ring_nf
        )
        all_goals norm_num
      · -- Prove 2 is in S
        use (fun x => x + 1)
        use (by
          intro x y
          simp [add_sq]
          <;> ring_nf
          <;> norm_num
          <;> ring_nf
          <;> try { nlinarith }
        )
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num