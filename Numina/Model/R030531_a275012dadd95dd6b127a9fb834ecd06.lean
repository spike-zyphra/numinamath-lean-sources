import Mathlib

theorem algebra_14008 (a d : ℝ) (S : ℕ → ℝ)
    (hS : ∀ n, S n = ∑ i in Finset.range n, (a + d * i)) (hS1 : S 5 * S 6 + 15 = 0) :
    d ≤ -2 * √2 ∨ d ≥ 2 * √2 := by
  have h1 : S 5 = 5 * (a + 2 * d) := by
    rw [hS 5]
    norm_num [Finset.sum_range_succ]
    all_goals ring

  have h2 : S 6 = 3 * (2 * a + 5 * d) := by
    rw [hS 6]
    norm_num [Finset.sum_range_succ]
    all_goals ring

  rw [h1, h2] at hS1

  have h7 : d ^ 2 ≥ 8 := by
    nlinarith [sq_nonneg (5 * a + 15 * d), sq_nonneg (4 * a + 9 * d)]

  have h8 : d ^ 2 - 8 ≥ 0 := by 
    linarith

  by_cases h9 : d ≥ 0
  · -- d >= 0
    have h10 : d ≥ 2 * Real.sqrt 2 := by
      have h11 : d ^ 2 ≥ 8 := h7
      have h12 : d ≥ Real.sqrt 8 := by
        have h13 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)]
      have h13 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [h12, h13]
    right
    linarith [h10]
    
  · -- d < 0
    have h9 : d < 0 := by 
      by_contra h
      push_neg at h
      have : d ≥ 0 := by linarith
      linarith
    have h10 : d ≤ -2 * Real.sqrt 2 := by
      have h7 : d ^ 2 ≥ 8 := h7
      have h11 : d ≤ -Real.sqrt 8 := by
        nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)]
      have h12 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [h11, h12]
    left
    linarith [h10]