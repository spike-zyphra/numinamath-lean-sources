import Mathlib

theorem algebra_71117 (x : ℝ) (hx : x ^ 4 = 2 * x ^ 2 + ⌊x⌋) :
    x = 0 ∨ x = Real.sqrt (1 + Real.sqrt 2) ∨ x = -1 := by 
  let n := ⌊x⌋
  have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h3 : (x : ℝ) ^ 4 = 2 * (x : ℝ) ^ 2 + (n : ℝ) := by linarith [hx]

  have h4 : n ≤ 2 := by
    by_contra h
    push_neg at h 
    have h5 : n ≥ 3 := by omega
    have h5 : (n : ℝ) ≥ (3 : ℝ) := by
      exact_mod_cast (show n ≥ 3 from by omega)
    nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x + 1), sq_nonneg (x - 1), 
          sq_nonneg (x - (n : ℝ)), sq_nonneg (x ^ 2 - 3), 
          h1, h2, sq_nonneg (x - 2)]
  
  have h5 : n ≥ -1 := by 
    by_contra h 
    push_neg at h 
    have h6 : n ≤ -2 := by omega 
    have h7 : (n : ℝ) ≤ (-2 : ℝ) := by 
      exact_mod_cast h6 
    nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x + 1), sq_nonneg (x - 1), 
          sq_nonneg (x - (n : ℝ)), sq_nonneg (x ^ 2 - 2), 
          h1, h2]
  
  have h6 : n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by 
    omega

  rcases h6 with (hn | hn | hn | hn)
  · -- Case n = -1 
    have hn1 : (n : ℝ) = (-1 : ℝ) := by 
      exact_mod_cast hn 
    rw [hn1] at h3 
    have h_eq : x ^ 4 = 2 * x ^ 2 - 1 := by linarith 
    have h_eq2 : (x + 1) * (x - 1) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), 
          sq_nonneg (x), h1, h2]
    cases' (mul_eq_zero.mp h_eq2) with h4 h5 
    · -- Case x + 1 = 0 
      right
      right 
      linarith 
    · -- Case x - 1 = 0 
      nlinarith
  · -- Case n = 0 
    have hn1 : (n : ℝ) = (0 : ℝ) := by 
      exact_mod_cast hn 
    rw [hn1] at h3 
    have h_eq : x ^ 4 = 2 * x ^ 2 := by linarith [h3] 
    have h_eq2 : x ^ 2 * (x  ^ 2 - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h_eq2) with h4 h5 
    · -- Case x ^ 2 = 0 
      left
      nlinarith 
    · -- Case x ^ 2 - 2 = 0 
      nlinarith [h1, h2, sq_nonneg (x ^ 2 - 2), sq_nonneg (x + 1)]
  · -- Case n = 1 
    have hn1 : (n : ℝ) = (1 : ℝ) := by 
      exact_mod_cast hn 
    rw [hn1] at h3 
    have h_eq : x ^ 4 = 2 * x ^ 2 + 1 := by linarith 
    have h8 : (x ^ 2 - (1 + Real.sqrt 2)) * (x ^ 2 - (1 - Real.sqrt 2)) = 0 := by
      nlinarith [ sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - (1 + Real.sqrt 2)), 
          Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    cases' (mul_eq_zero.mp h8) with h9 h10 
    · -- Case x ^ 2 - (1 + Real.sqrt 2) = 0
      have h11 : x ^ 2 = 1 + Real.sqrt 2 := by linarith
      have h12 : x = Real.sqrt (1 + Real.sqrt 2) ∨ x = - Real.sqrt (1 + Real.sqrt 2) := by 
        have h13 : x ^ 2 = 1 + Real.sqrt 2 := h11 
        have : x = Real.sqrt (1 + Real.sqrt 2) ∨ x = - Real.sqrt (1 + Real.sqrt 2) := by 
          apply eq_or_eq_neg_of_sq_eq_sq 
          field_simp 
          linarith 
        tauto 
      cases h12 with
      | inl h14 => 
        right 
        left 
        tauto 
      | inr h15 => 
        nlinarith [ Real.sqrt_nonneg (1 + Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + Real.sqrt 2 : ℝ) by positivity) ]
    · -- Case x ^ 2 - (1 - Real.sqrt 2) = 0 
      nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  · -- Case n = 2 
    have hn1 : (n : ℝ) = (2 : ℝ) := by 
      exact_mod_cast hn 
    rw [hn1] at h3 
    nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x + 1), sq_nonneg (x - 1), 
          sq_nonneg (x - (n : ℝ)), sq_nonneg (x ^ 2 - 2), 
          h1, h2, sq_nonneg (x - 2)]