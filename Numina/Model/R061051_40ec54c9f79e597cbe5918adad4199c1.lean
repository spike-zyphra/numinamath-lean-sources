import Mathlib

open Real

theorem algebra_4036 (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (h : ∑ i ∈ Finset.range (k + 1), (1 / (sqrt (n + i) + sqrt (n + i + 1))) = 9) :
    k ≥ 98 := by 
  have h1 : ∀ i : ℕ, 1 / (sqrt (n + i) + sqrt (n + i + 1)) = sqrt (n + i + 1) - sqrt (n + i) := by
    intro i
    have h2 : sqrt (n + i + 1) + sqrt (n + i) ≠ 0 := by 
      have h3 : sqrt (n + i + 1) ≥ 0 := by positivity
      have h4 : sqrt (n + i) ≥ 0 := by positivity
      by_contra h
      have : sqrt (n + i + 1) = 0 := by linarith [h3, h4, h]
      have : (n + i + 1 : ℝ) = 0 := by 
        rw [Real.sqrt_eq_zero (by positivity)] at this
        linarith
      have h5 : (n + i + 1 : ℝ) ≥ 1 := by 
        have hn' : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by omega)
        have : (i + 1 : ℝ) ≥ 0 := by positivity
        linarith 
      linarith 
    field_simp [h2]
    <;> ring_nf <;> rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    <;> ring 
  have h2 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (1 / (sqrt (n + i) + sqrt (n + i + 1))) = sqrt (n + k) - sqrt n := by 
    intro k 
    induction k with 
    | zero =>
      simp 
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h1]
      <;> ring_nf <;> rw [Real.sqrt_inj (by positivity) (by positivity)] <;> linarith 
  have h3 := h2 (k + 1)
  rw [h3] at h
  have h4 : sqrt (n + k + 1 : ℝ) = sqrt (n : ℝ) + 9 := by 
    have h5 : sqrt (n + (k + 1 : ℕ)) = sqrt (n + k + 1 : ℝ) := by 
      norm_num 
      <;> ring_nf 
    simp [h5] at *
    linarith 
  have h5 : ((sqrt (n : ℝ) + 9) : ℝ) ^ 2 = ((sqrt (n + k + 1 : ℝ)) : ℝ) ^ 2 := by 
    rw [h4]
  have h6 : ((sqrt (n : ℝ) + 9 : ℝ) ^ 2) = ((sqrt (n : ℝ) : ℝ) ^ 2) + 18 * (sqrt (n : ℝ) : ℝ) + 81 := by 
    nlinarith 
  have h7 : ((sqrt (n + k + 1 : ℝ) : ℝ) ^ 2) = (n + k + 1 : ℝ) := by 
    have h8 : ((sqrt (n + k + 1 : ℝ) : ℝ) ^ 2) = (n + k + 1 : ℝ) := by 
      rw [Real.sq_sqrt]
      positivity 
    linarith 
  rw [h6] at h5 
  rw [h7] at h5 
  have h8 : ((sqrt (n : ℝ) : ℝ) ^ 2) = (n : ℝ) := by 
    have h9 : ((sqrt (n : ℝ) : ℝ) ^ 2) = (n : ℝ) := by 
      rw [Real.sq_sqrt]
      positivity 
    linarith 
  rw [h8] at h5 
  have h9 : (k : ℝ) = 18 * (sqrt (n : ℝ) : ℝ) + 80 := by 
    nlinarith 
  have h10 : (k : ℝ) ≥ 98 := by 
    nlinarith [Real.sqrt_nonneg (n : ℝ), show (n : ℝ) ≥ 1 by exact_mod_cast (show n ≥ 1 by omega), Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  have h11 : k ≥ 98 := by 
    exact_mod_cast h10 
  linarith