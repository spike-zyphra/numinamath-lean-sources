import Mathlib

theorem inequalities_277230 (a b c : ℝ) (h : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → |a * x^2 + b * x + c| ≤ 1) :
    ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → |c * x^2 + b * x + a| ≤ 2 := by
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h (0) (by norm_num)
  have h11 : -1 ≤ a + b + c := by
    cases abs_le.mp h1 with
    | intro h11 h12 =>
      linarith
  have h12 : a + b + c ≤ 1 := by
    cases abs_le.mp h1 with
    | intro h11 h12 =>
      linarith
  have h13 : -1 ≤ a - b + c := by
    cases abs_le.mp h2 with
    | intro h21 h22 =>
      linarith
  have h14 : a - b + c ≤ 1 := by
    cases abs_le.mp h2 with
    | intro h21 h22 =>
      linarith
  have h31 : -1 ≤ c := by
    cases abs_le.mp h3 with
    | intro h31 h32 =>
      linarith
  have h32 : c ≤ 1 := by
    cases abs_le.mp h3 with
    | intro h31 h32 =>
      linarith
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  have hx3 : -1 ≤ x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hx4 : x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg x]
  apply abs_le.mpr
  constructor
  · -- Proving the lower bound: c * x^2 + b * x + a ≥ -2
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
  · -- Proving the upper bound: c * x^2 + b * x + a ≤ 2
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]