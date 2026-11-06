import Mathlib

theorem algebra_2661 {x : Fin 4 → ℝ} (hx : ∀ i, x i = 1 / 11 ^ ((1 : ℝ) / 10)) :
    ∀ i j, i ≠ j → ∑ k ∈ Finset.range 11, x i ^ (10 - k) * x j ^ k = 1 := by 
  intro i j hne
  have h1 : x i = x j := by
    have h2 : x i = 1 / 11 ^ ((1 : ℝ) / 10) := by
      apply hx
    have h3 : x j = 1 / 11 ^ ((1 : ℝ) / 10) := by
      apply hx
    rw [h2, h3]
  
  rw [show x j = x i by linarith [h1]]
  have h2 : ∑ k in Finset.range 11, x i ^ (10 - k) * (x i) ^ k = 11 * (x i ^ 10) := by
    simp [Finset.sum_range_succ]
    all_goals
      ring_nf
  rw [h2]
  have h3 : x i ^ 10 = 1 / 11 := by
    rw [hx i]
    have h4 : (1 / 11 ^ ((1 : ℝ) / 10) : ℝ) ^ 10 = 1 / 11 := by
      have h5 : (11 ^ ((1 : ℝ) / 10) : ℝ) ^ 10 = (11 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      calc 
        (1 / 11 ^ ((1 : ℝ) / 10) : ℝ) ^ 10
          = 1 / ((11 ^ ((1 : ℝ) / 10) : ℝ) ^ 10) := by 
            field_simp
        _ = 1 / (11 : ℝ) := by 
          rw [h5]
        _ = (1 / 11 : ℝ) := by 
          norm_num
    linarith
  rw [h3]
  all_goals norm_num