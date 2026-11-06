import Mathlib

theorem algebra_288867 :
  {c : ℝ | ∃ x, x^5 - 5 * x + c = 0 ∧ deriv (fun x => x^5 - 5 * x + c) x = 0} =
  {4, -4} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume there exists such an x
    rintro ⟨x, h1, h2⟩
    have h3 : deriv (fun (y : ℝ) => y ^ 5 - 5 * y + c) x = 5 * x ^ 4 - 5 := by
      simp [deriv_pow, deriv_const, deriv_sub, deriv_add, mul_comm]
      <;> field_simp
      <;> ring
    rw [h3] at h2
    have h4 : x ^ 4 = 1 := by
      nlinarith 
    have h5 : x = 1 ∨ x = -1 := by
      have h6 : x ^ 4 - 1 = 0 := by linarith
      have h7 : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
        ring_nf at h6 ⊢
        linarith
      cases (mul_eq_zero.1 h7) with
      | inl h8 =>
        have h9 : x ^ 2 = 1 := by linarith 
        have : x = 1 ∨ x = -1 := by 
          have h10 : x ^ 2 = 1 := h9 
          have : x = 1 ∨ x = -1 := by 
            rw [sq_eq_one_iff] at h10 
            tauto 
          assumption 
        assumption
      | inr h8 =>
        have h9 : x ^ 2 = -1 := by linarith 
        nlinarith [sq_nonneg x]
    cases h5 with
    | inl h5 =>
      rw [h5] at h1 
      left 
      linarith 
    | inr h5 =>
      rw [h5] at h1 
      right 
      linarith 
  · -- Show that {4, -4} is contained in the set
    rintro (h | h)
    · -- Assume c = 4
      rw [h]
      use 1 
      constructor
      · -- Show $1^5 - 5 * 1 + 4 = 0$
        norm_num 
      · -- Show derivative at 1 is 0
        norm_num [deriv_pow, deriv_const, deriv_sub, deriv_add, mul_comm]
    · -- Assume c = -4
      rw [h]
      use -1 
      constructor 
      · -- Show $(-1)^5 - 5*(-1) -4 = 0$
        norm_num 
      · -- Show derivative at -1 is 0
        norm_num [deriv_pow, deriv_const, deriv_sub, deriv_add, mul_comm]