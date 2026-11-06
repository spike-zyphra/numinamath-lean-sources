import Mathlib

theorem inequalities_70975 (a b c d : ℝ) :
    (∀ x : ℝ, |x| ≤ 1 → |a * x^3 + b * x^2 + c * x + d| ≤ 1) ∧
    a * 2^3 + b * 2^2 + c * 2 + d = 26 ↔ (a, b, c, d) = (4, 0, -3, 0) := by
  constructor
  · -- Forward: both conditions hold implies the coefficients
    rintro ⟨h, heq⟩
    have h1 := h 1 (by norm_num)
    have h2 := h (-1) (by norm_num)
    have h3 := h (1 / 2) (by
      norm_num [abs_le]
    )
    have h4 := h (-1 / 2) (by
      norm_num [abs_le]
    )
    have h5 := h 0 (by norm_num)
    -- Extract inequalities
    have h11 : -1 ≤ a * (1 : ℝ) ^ 3 + b * (1 : ℝ) ^ 2 + c * (1 : ℝ) + d := by 
      cases' abs_le.mp h1 with h12 h13
      linarith 
    have h12 : a * (1 : ℝ) ^ 3 + b * (1 : ℝ) ^ 2 + c * (1 : ℝ) + d ≤ 1 := by 
      cases' abs_le.mp h1 with h12 h13
      linarith 
    -- For x = -1: 
    have h21 : -1 ≤ a * (-1 : ℝ) ^ 3 + b * (-1 : ℝ) ^ 2 + c * (-1 : ℝ) + d := by 
      cases' abs_le.mp h2 with h22 h23 
      linarith 
    have h22 : a * (-1 : ℝ) ^ 3 + b * (-1 : ℝ) ^ 2 + c * (-1 : ℝ) + d ≤ 1 := by 
      cases' abs_le.mp h2 with h22 h23 
      linarith 
    -- For x = 1/2: 
    have h31 : -1 ≤ a * (1 / 2 : ℝ) ^ 3 + b * (1 / 2 : ℝ) ^ 2 + c * (1 / 2 : ℝ) + d := by 
      cases' abs_le.mp h3 with h32 h33 
      linarith 
    have h32 : a * (1 / 2 : ℝ) ^ 3 + b * (1 / 2 : ℝ) ^ 2 + c * (1 / 2 : ℝ) + d ≤ 1 := by 
      cases' abs_le.mp h3 with h32 h33 
      linarith 
    -- For x = -1/2: 
    have h41 : -1 ≤ a * (-1 / 2 : ℝ) ^ 3 + b * (-1 / 2 : ℝ) ^ 2 + c * (-1 / 2 : ℝ) + d := by 
      cases' abs_le.mp h4 with h42 h43 
      linarith 
    have h42 : a * (-1 / 2 : ℝ) ^ 3 + b * (-1 / 2 : ℝ) ^ 2 + c * (-1 / 2 : ℝ) + d ≤ 1 := by 
      cases' abs_le.mp h4 with h42 h43 
      linarith 
    -- For x = 0: 
    have h51 : -1 ≤ a * (0 : ℝ) ^ 3 + b * (0 : ℝ) ^ 2 + c * (0 : ℝ) + d := by 
      cases' abs_le.mp h5 with h52 h53 
      linarith 
    have h52 : a * (0 : ℝ) ^ 3 + b * (0 : ℝ) ^ 2 + c * (0 : ℝ) + d ≤ 1 := by 
      cases' abs_le.mp h5 with h52 h53 
      linarith 
    have ha1 : a = 4 := by
      ring_nf at heq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
      nlinarith 
    have hb1 : b = 0 := by
      ring_nf at heq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
      nlinarith 
    have hc1 : c = -3 := by
      ring_nf at heq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
      nlinarith
    have hd1 : d = 0 := by
      ring_nf at heq h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
      nlinarith 
    simp [Prod.ext_iff, ha1, hb1, hc1, hd1]
    all_goals linarith 
  · -- Backward: coefficients satisfy both conditions
    rintro h 
    rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
    constructor 
    · -- Show that for all |x| ≤ 1, |f(x)| ≤ 1
      intro x hx
      have h1 : -1 ≤ x := by 
        cases' abs_le.mp hx with h2 h3 
        linarith
      have h2 : x ≤ 1 := by 
        cases' abs_le.mp hx with h3 h4 
        linarith 
      have h3 : -1 ≤ 4 * x ^ 3 + (0 : ℝ) * x ^ 2 + (-3 : ℝ) * x + (0 : ℝ) := by
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x + 1), sq_nonneg (x - 1), mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x + 1 by linarith)]
      have h4 : 4 * x ^ 3 + (0 : ℝ) * x ^ 2 + (-3 : ℝ) * x + (0 : ℝ) ≤ 1 := by 
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x + 1), sq_nonneg (x - 1), mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x + 1 by linarith)]
      apply abs_le.mpr
      constructor <;> nlinarith 
    · -- Show that f(2) = 26
      norm_num