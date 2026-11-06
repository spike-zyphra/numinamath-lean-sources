import Mathlib

theorem algebra_15519 (f : ℝ → ℝ) (hf : f = fun x => 15 * x ^ 4 - 13 * x ^ 2 + 2) :
    IsGreatest {x | f x = 0} (Real.sqrt 6 / 3) := by
  have h1 : ∀ x, f x = 15 * x ^ 4 - 13 * x ^ 2 + 2 := by
    intro x
    rw [hf]

  have h2 : f (Real.sqrt 6 / 3) = 0 := by
    rw [h1]
    have h3 : (Real.sqrt 6 : ℝ) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
    have h4 : (Real.sqrt 6 / 3 : ℝ) ^ 2 = (2 / 3 : ℝ) := by
      calc
        (Real.sqrt 6 / 3 : ℝ) ^ 2 = (Real.sqrt 6 : ℝ) ^ 2 / 9 := by ring_nf
        _ = (6 / 9 : ℝ) := by rw [h3]
        _ = (2 / 3 : ℝ) := by norm_num
    have h5 : (Real.sqrt 6 / 3 : ℝ) ^ 4 = (4 / 9 : ℝ) := by
      calc
        (Real.sqrt 6 / 3 : ℝ) ^ 4 = ((Real.sqrt 6 / 3 : ℝ) ^ 2) ^ 2 := by ring_nf
        _ = (2 / 3 : ℝ) ^ 2 := by rw [h4]
        _ = (4 / 9 : ℝ) := by norm_num
    nlinarith

  constructor
  · -- Verify that √6/3 is a root of f(x) = 0
    exact h2
  · -- Now show that if x is a root, x ≤ √6/3
    intro x hx
    have hfx : f x = 0 := hx
    rw [h1] at hfx
    have h3 : 15 * x ^ 4 - 13 * x ^ 2 + 2 = 0 := hfx
    have h4 : 15 * (x ^ 2 - 2 / 3) * (x ^ 2 - 1 / 5) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2 / 3), sq_nonneg (x ^ 2 - 1 / 5)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case 1: x ^ 2 = 2/3
      have h7 : x ^ 2 = (2 / 3 : ℝ) := by
        nlinarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 6 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    · -- Case 2: x ^ 2 = 1/5
      have h8 : x ^ 2 = (1 / 5 : ℝ) := by
        nlinarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 6 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]