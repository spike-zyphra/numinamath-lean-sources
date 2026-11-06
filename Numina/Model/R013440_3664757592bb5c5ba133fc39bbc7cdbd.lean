import Mathlib

open Real

theorem algebra_218302 {a : ℝ} (ha : a > 1) (y : ℝ → ℝ)
    (hy : ∀ x, y x = (a ^ x + a ^ (-x)) / 2) :
    ∀ x, y x + sqrt ((y x) ^ 2 - 1) ≥ 1 := by
  intro x
  have h1 : y x ≥ 1 := by
    rw [hy x]
    have h11 : a ^ x + a ^ (-x) ≥ 2 := by
      have h3 : a ^ x > 0 := by positivity
      have h4 : a ^ (-x) > 0 := by positivity 
      have h5 : a ^ x * (a ^ (-x)) = 1 := by
        have h9 : a ^ x * (a ^ (-x)) = a ^ (x + (-x)) := by 
          rw [← Real.rpow_add]
          ring_nf
          all_goals linarith
        have h10 : a ^ (x + (-x)) = a ^ (0 : ℝ) := by 
          ring_nf
        have h11 : a ^ (0 : ℝ) = 1 := by 
          simp [pow_zero]
        rw [h10, h11] at h9
        linarith
      nlinarith [sq_nonneg (a ^ x - 1), sq_nonneg (a ^ (-x) - 1), 
        mul_pos (show 0 < (a ^ x : ℝ) by positivity) (show 0 < (a ^ (-x) : ℝ) by positivity)]
    have h12 : (a ^ x + a ^ (-x) ) / 2 ≥ 1 := by 
      linarith [h11]
    linarith
  have h4 : (y x) ^ 2 - 1 ≥ 0 := by
    nlinarith [sq_nonneg (y x - 1), h1]
  have h5 : sqrt ((y x) ^ 2 - 1) ≥ 0 := Real.sqrt_nonneg ((y x) ^ 2 - 1)
  nlinarith [Real.sqrt_nonneg ((y x) ^ 2 - 1), Real.sq_sqrt (show (y x) ^ 2 - 1 ≥ 0 by linarith [h4]), h1, sq_nonneg (sqrt ((y x) ^ 2 - 1) ) ]