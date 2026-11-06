import Mathlib

theorem algebra_232309 :
   {n | ∃ x : ℤ, x^3 - n * x^2 + n * x - (n^2 + 1) = 0} = {0, -3} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor 
  · -- Assuming there's an integer x satisfying the polynomial equation 
    rintro ⟨x, hx⟩ 
    have h_eq1 : (x - n) * (x^2 + n) = 1 := by 
      nlinarith [sq_nonneg (x ^2), sq_nonneg ((x - n) : ℤ), sq_nonneg ((x + 1) : ℤ), sq_nonneg ((n + 3) : ℤ), sq_nonneg (x - (n) + 1 : ℤ)]
    have h1 : (x - n) = 1 ∨ (x - n) = -1 := by 
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h_eq1 
    rcases h1 with (h1 | h1)
    · -- Case 1: $h1 : x -n = 1$ 
      have h2 : x^2 + n = 1 := by 
        rw [h1] at h_eq1 
        linarith 
      have h3 : x = n + 1 := by linarith 
      rw [h3] at h2 
      have h4 : n * (n + 3) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h4) with h5 h6 
      · -- Case 1a: n = 0 
        left 
        linarith 
      · -- Case 1b: n = -3 
        right 
        linarith 
    · -- Case 2: $h1 : x -n = -1$ 
      have h2 : x^2 + n = -1 := by 
        rw [h1] at h_eq1 
        linarith 
      have h3 : x = n - 1 := by linarith 
      rw [h3] at h2 
      have h4 : n ^ 2 - n + 2 = 0 := by 
        nlinarith 
      nlinarith [sq_nonneg (n : ℤ)] 
  · -- Show the converse: if n ∈ {0, -3}, then ∃ x : ℤ, x^3 - n * x^2 + n * x - (n^2 + 1) = 0 
    rintro (rfl | rfl)
    · -- n = 0 
      use 1 
      norm_num 
    · -- n = -3 
      use -2 
      norm_num