import Mathlib

open Real Set
open scoped Real

theorem algebra_230063 (x : ℝ) :
  2 * (cos x)^2 + sqrt (cos x) = 3 ↔ ∃ n : ℤ, x = 2 * π * n := by
  constructor
  · -- Assume 2 * (cos x)^2 + sqrt (cos x) = 3, prove ∃ n : ℤ, x = 2 * π * n
    intro h
    have h1 : cos x ≥ 0 := by
      by_contra h1
      push_neg at h1
      have h2 : sqrt (cos x) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals linarith
      rw [h2] at h
      nlinarith [cos_le_one x, neg_one_le_cos x]
    have h2 : sqrt (cos x) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : sqrt (cos x) = 1 := by
      nlinarith [sq_nonneg (sqrt (cos x) ^ 2 - 1), sq_nonneg (sqrt (cos x) - 1), 
          Real.sq_sqrt (show (0 : ℝ) ≤ cos x by linarith), 
          cos_le_one x, neg_one_le_cos x]
    have h6 : cos x = 1 := by
      calc
        cos x = (sqrt (cos x)) ^ 2 := by rw [Real.sq_sqrt]; all_goals linarith
        _ = (1 : ℝ) ^ 2 := by rw [h4]
        _ = (1 : ℝ) := by norm_num
    have h7 : ∃ n : ℤ, x = 2 * π * n := by
      have h8 : cos x = 1 := h6
      have h9 : ∃ n : ℤ, x = 2 * π * n := by
        rw [Real.cos_eq_one_iff] at h8
        rcases h8 with ⟨n, hn⟩
        use n
        linarith
      exact h9
    exact h7
  · -- Assume ∃ n : ℤ, x = 2 * π * n, prove 2 * (cos x)^2 + sqrt (cos x) = 3
    rintro ⟨n, hn⟩
    have h10 : cos x = 1 := by
      rw [hn]
      have h11 : cos (2 * π * (n : ℝ)) = 1 := by
        have h12 : 2 * π * (n : ℝ) = (n : ℝ) * (2 * π) := by ring
        rw [h12]
        rw [Real.cos_int_mul_two_pi]
      exact h11
    rw [h10]
    have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
    rw [h11]
    nlinarith