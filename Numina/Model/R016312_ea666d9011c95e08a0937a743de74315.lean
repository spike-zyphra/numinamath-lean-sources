import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253740 (x y : ℝ) :
  -abs y + x - sqrt (x^2 + y^2 - 1) ≥ 1 ↔ (x, y) = (1, 0) := by
  constructor
  · -- Assume -abs y + x - sqrt (x^2 + y^2 - 1) ≥ 1, prove (x, y) = (1, 0)
    intro h
    have h1 : x ^ 2 + y ^ 2 ≥ 1 := by
      by_contra h2
      push_neg at h2
      have h3 : x ^ 2 + y ^ 2 - 1 < 0 := by linarith [h2]
      have h4 : Real.sqrt (x ^ 2 + y ^ 2 - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals
          nlinarith [show x ^ 2 + y ^ 2 - 1 < 0 by linarith [h3]]
      rw [h4] at h
      nlinarith [abs_nonneg y, sq_nonneg (x - 1), sq_nonneg y]
    have h2 : Real.sqrt (x ^ 2 + y ^ 2 - 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2 - 1)
    have h3 : -abs y + x - Real.sqrt (x ^ 2 + y ^ 2 - 1) ≥ 1 := h
    have h9 : x - abs y ≥ 1 + Real.sqrt (x ^ 2 + y ^ 2 - 1) := by
      linarith
    have h4 : Real.sqrt (x ^ 2 + y ^ 2 - 1) ≤ x - abs y - 1 := by
      nlinarith
    have h7 : (Real.sqrt (x ^ 2 + y ^ 2 - 1)) ^ 2 = x ^ 2 + y ^ 2 - 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : (Real.sqrt (x ^ 2 + y ^ 2 - 1)) ^ 2 ≤ (x - abs y - 1) ^ 2 := by
      nlinarith [h4, Real.sqrt_nonneg (x ^ 2 + y ^ 2 - 1)]
    have h11 : x ≥ abs y + 1 := by
      cases' abs_cases y with hy1 hy1
      · -- y ≥ 0, so abs y = y
        nlinarith [abs_nonneg y, h4, h9]
      · -- y < 0, so abs y = -y
        nlinarith [abs_nonneg y, h4, h9]
    have h12 : x ≤ 1 := by
      cases' abs_cases y with hy1 hy1
      · -- y ≥ 0, abs y = y
        nlinarith [h7, h5, sq_nonneg (x - (abs y + 1)), sq_nonneg (y - 0)]
      · -- y < 0, abs y = -y
        nlinarith [h7, h5, sq_nonneg (x - (abs y + 1)), sq_nonneg (y + 0)]
    have h13 : x = 1 := by
      cases' abs_cases y with hy1 hy1
      · -- y ≥ 0, abs y = y
        nlinarith
      · -- y < 0, abs y = -y
        nlinarith
    have h14 : y = 0 := by
      cases' abs_cases y with hy1 hy1
      · -- y ≥ 0, abs y = y
        nlinarith [h13]
      · -- y < 0, abs y = -y
        nlinarith [h13]
    simp [h13, h14]
  · -- Assume (x, y) = (1, 0), prove -abs y + x - sqrt (x^2 + y^2 - 1) ≥ 1
    rintro ⟨rfl, rfl⟩
    have h10 : sqrt (1 ^ 2 + (0: ℝ) ^ 2 - 1) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    rw [h10]
    norm_num [abs_of_nonneg]