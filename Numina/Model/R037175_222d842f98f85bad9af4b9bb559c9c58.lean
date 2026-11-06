import Mathlib

theorem algebra_21911 :
    {x : ℂ | ∃(b : ℂ), x^2 - 7 * x + b = 0 ∧ x^2 + 2 * x - 2 * b = 0} = {0, 4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume that x is a common root of both polynomials.
    rintro ⟨b, h₁, h₂⟩
    have h3 : b = 3 * x := by
      have eq2 : (x ^ 2 -7 * x + b) - (x ^ 2 + 2 * x - 2 * b) = 0 := by
        rw [h₁, h₂]
        all_goals norm_num
      have eq3 : (x ^ 2 -7 * x + b) - (x ^ 2 + 2 * x - 2 * b) = 
          -9 * x + 3 * b := by 
        ring_nf
      rw [eq3] at eq2
      have h6 : -9 * x + 3 * b = 0 := by 
        simpa using eq2
      have h10 : b = 3 * x := by 
        calc
          b = (3 * b) / 3 := by field_simp [show (3 : ℂ) ≠ 0 by norm_num]
          _ = (9 * x) / 3 := by 
            have h4 : 3 * b = 9 * x := by 
              calc 
                3 * b = (-9 * x + 3 * b) + 9 * x := by ring_nf
                _ = 0 + 9 * x := by rw [h6]
                _ = 9 * x := by ring_nf
            rw [h4]
          _ = 3 * x := by 
            field_simp [show (3 : ℂ) ≠ 0 by norm_num]
            <;> ring_nf
      exact h10
    rw [h3] at h₁
    have h5 : x ^ 2 - 4 * x = 0 := by 
      simp [pow_two, Complex.ext_iff] at h₁ ⊢
      ring_nf at h₁ ⊢
      constructor
      · ring_nf at h₁ ⊢
        linarith
      all_goals 
        try tauto
    have h6 : x = 0 ∨ x = 4 := by 
      have h9 : x * (x - 4) = 0 := by 
        calc 
          x * (x - 4) = x ^ 2 - 4 * x := by ring_nf
          _ = 0 := h5
      cases' (mul_eq_zero.mp h9) with h10 h11
      · left 
        exact h10
      · right 
        exact eq_of_sub_eq_zero h11
    tauto 
  · -- Assume x is in {0,4}
    intro h 
    rcases h with (rfl | rfl)
    · 
      use 0 
      constructor 
      · norm_num 
      · norm_num 
    · 
      use 12 
      constructor 
      · norm_num [pow_two] 
      · norm_num [pow_two]