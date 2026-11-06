import Mathlib

theorem algebra_608382 (r s : ℕ) (hr : r > 0) (hs : s > 0) (h : Nat.Coprime r s) (h1 : r / s = (2 * (√2 + √10)) / (5 * (√(3 + √5)))) : r = 4 ∧ s = 5:= by
  have h2 : (r : ℝ) / (s : ℝ) = (2 * (√2 + √10)) / (5 * (√(3 + √5))) := by
    exact_mod_cast h1
  have h3 : (2 * (√2 + √10)) / (5 * (√(3 + √5))) = (4 / (5 : ℝ)) := by
    have h4 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h10 : √10 = √2 * √5 := by
      have h11 : (10 : ℝ) = 2 * 5 := by norm_num
      rw [h11]
      have h12 : √(2 * 5) = √2 * √5 := by
        rw [Real.sqrt_mul (by norm_num)]
      linarith [h12]
    have h6 : √(3 + √5) = (√2 * (1 + √5)) / 2 := by
      have h7 : ((√2 * (1 + √5)) / 2) ^ 2 = (3 + √5) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5)]
      have h8 : 0 ≤ (√2 * (1 + √5)) / 2 := by
        positivity
      rw [← h7]
      field_simp [Real.sqrt_sq h8]
    rw [h6, h10]
    field_simp [Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sqrt_nonneg (_ : ℝ)]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5)]
  rw [h3] at h2
  have h3' : (r : ℝ) * 5 = 4 * (s : ℝ) := by
    have h4 : (s : ℝ) ≠ 0 := by positivity
    field_simp at h2
    linarith
  have h4 : r * 5 = 4 * s := by
    exact_mod_cast h3'
  have h5 : r ∣ 4 * s := by
    use 5
    linarith
  have h6 : r ∣ 4 := by
    exact Nat.Coprime.dvd_of_dvd_mul_right h h5
  have h7 : r = 1 ∨ r = 2 ∨ r = 4 := by
    have : r ≤ 4 := by
      exact Nat.le_of_dvd (by linarith) h6
    interval_cases r <;> try tauto
  rcases h7 with (h7 | h7 | h7)
  · -- r = 1
    rw [h7] at h4
    omega
  · -- r = 2
    rw [h7] at h4
    omega
  · -- r = 4
    have h8 : s = 5 := by
      rw [h7] at h4
      omega
    exact ⟨h7, h8⟩