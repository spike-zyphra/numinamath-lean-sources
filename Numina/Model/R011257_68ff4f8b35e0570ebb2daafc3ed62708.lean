import Mathlib

theorem algebra_23714 (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i)(a : ℝ )(ha : a ≥ 0)
    (h1 : ∑ i, (i + 1) * x i = a) (h2 : ∑ i, (i + 1)^3 * x i = a^2)
    (h3 : ∑ i, (i + 1)^5 * x i = a^3) :
    a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 9 ∨ a = 16 ∨ a = 25 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h1 h2 h3
  have h4 : 0 ≤ x 0 := hx 0  
  have h5 : 0 ≤ x 1 := hx 1
  have h6 : 0 ≤ x 2 := hx 2
  have h7 : 0 ≤ x 3 := hx 3
  have h8 : 0 ≤ x 4 := hx 4
  have h9 : (a - 0) * (a - 1) * (a - 4) * (a - 9) * (a - 16) * (a - 25) = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3), sq_nonneg (x 4),
      sq_nonneg (a - 0), sq_nonneg (a - 1), sq_nonneg (a - 4), sq_nonneg (a - 9), sq_nonneg (a - 16), sq_nonneg (a - 25),
      mul_nonneg (show 0 ≤ x 0 by apply hx) (show 0 ≤ x 1 by apply hx),
      mul_nonneg (show 0 ≤ x 0 by apply hx) (show 0 ≤ x 2 by apply hx),
      mul_nonneg (show 0 ≤ x 0 by apply hx) (show 0 ≤ x 3 by apply hx),
      mul_nonneg (show 0 ≤ x 0 by apply hx) (show 0 ≤ x 4 by apply hx),
      mul_nonneg (show 0 ≤ x 1 by apply hx) (show 0 ≤ x 2 by apply hx),
      mul_nonneg (show 0 ≤ x 1 by apply hx) (show 0 ≤ x 3 by apply hx),
      mul_nonneg (show 0 ≤ x 1 by apply hx) (show 0 ≤ x 4 by apply hx),
      mul_nonneg (show 0 ≤ x 2 by apply hx) (show 0 ≤ x 3 by apply hx),
      mul_nonneg (show 0 ≤ x 2 by apply hx) (show 0 ≤ x 4 by apply hx),
      mul_nonneg (show 0 ≤ x 3 by apply hx) (show 0 ≤ x 4 by apply hx)
    ]
  cases' (mul_eq_zero.mp h9) with h4 h5
  cases' (mul_eq_zero.mp h4) with h4 h6
  cases' (mul_eq_zero.mp h4) with h4 h7
  cases' (mul_eq_zero.mp h4) with h4 h8
  cases' (mul_eq_zero.mp h4) with h4 h9
  · -- h9: a - 0 = 0  
    have h10 : a = 0 := by linarith
    simp [h10]
  · -- h12: a - 1 = 0
    have h10 : a = 1 := by linarith
    simp [h10]
  · -- h8: a - 4 = 0
    have h10 : a = 4 := by linarith
    simp [h10]
  · -- h7: a - 9 = 0
    have h10 : a = 9 := by linarith
    simp [h10]
  · -- h6: a - 16 = 0
    have h10 : a = 16 := by linarith
    simp [h10]
  · -- h5: a - 25 = 0
    have h10 : a = 25 := by linarith
    simp [h10]