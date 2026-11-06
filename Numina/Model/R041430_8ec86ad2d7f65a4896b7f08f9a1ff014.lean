import Mathlib

open Real

theorem inequalities_599425 (m : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b + c = 1 → m * (a^3 + b^3 + c^3) ≥
      6 * (a^2 + b^2 + c^2) + 1) ↔ m ≥ 27 := by
  constructor
  · -- Reverse is not true
    intro h
    have h1 := h (1 / 3) (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1 ⊢
    nlinarith
  · -- Forward
    intro hm a b c ha hb hc h2
    have h1 : a + b + c = 1 := h2
    have eq1 : a^3 + b^3 + c^3 = 1 - 3 * (a * b + a * c + b * c) + 3 * (a * b * c) := by
      have h3 : a + b + c = 1 := h1
      have h4 : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + a * c + b * c) + 3 * (a * b * c) := by
        ring
      rw [show a + b + c = 1 by linarith [h3]] at h4
      linarith
    have eq2 : a ^ 2 + b ^ 2 + c ^ 2 = 1 - 2 * (a * b + a * c + b * c) := by
      have h5 : a + b + c = 1 := h1
      have h6 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
        ring
      rw [show a + b + c = 1 by linarith [h5]] at h6
      linarith
    have eq3 : 27 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 6 * (a^2 + b^2 + c^2) + 1 := by
      rw [eq1, eq2]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3), h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    have h2' : m * (a^3 + b^3 + c^3) ≥ 6 * (a^2 + b^2 + c^2) + 1 := by
      have h3' : m ≥ 27 := hm
      have h7 : m * (a^3 + b^3 + c^3) ≥ 27 * (a^3 + b^3 + c^3) := by
        have h5 : a^3 + b^3 + c^3 ≥ 0 := by
          positivity
        nlinarith
      have h8 : 27 * (a^3 + b^3 + c^3) ≥ 6 * (a^2 + b^2 + c^2) + 1 := eq3
      linarith
    linarith