import Mathlib

theorem algebra_232871 (x : ℝ) (hx : x > 2022) :min (min (min (min (x / 2022) (2022 / (x - 1))) (2022 / x)) ((x + 1) / 2022)) (2022 / (x + 1)) = 2022 / (x + 1) := by
  have h1 : x - 1 > 0 := by linarith
  have h2 : x + 1 > 0 := by linarith
  have h3 : 2022 / (x + 1) ≤ x / 2022 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [show x ^ 2 ≥ (2022 : ℝ) ^ 2 by nlinarith, show x > 0 by linarith]
  have h4 : 2022 / (x + 1) ≤ 2022 / (x - 1) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [show x - 1 > 0 by linarith]
  have h5 : 2022 / (x + 1) ≤ 2022 / x := by
    have hx_pos : x > 0 := by linarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [show x > 0 by linarith]
  have h6 : 2022 / (x + 1) ≤ (x + 1) / 2022 := by
    have h7 : (x + 1) ^ 2 ≥ (2022 : ℝ) ^ 2 := by
      nlinarith [show x ^ 2 ≥ (2022 : ℝ) ^ 2 by nlinarith, show x > 0 by linarith]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h7]
  have h7 : min (min (min (min (x / 2022) (2022 / (x - 1))) (2022 / x)) ((x + 1) / 2022)) (2022 / (x + 1)) = 2022 / (x + 1) := by
    have h19 : 2022 / (x + 1) ≤ (min (min (min (x / 2022) (2022 / (x - 1))) (2022 / x)) ((x + 1) / 2022)) := by
      have h20 : 2022 / (x + 1) ≤ x / 2022 := h3
      have h21 : 2022 / (x + 1) ≤ 2022 / (x - 1) := h4
      have h22 : 2022 / (x + 1) ≤ 2022 / x := h5
      have h23 : 2022 / (x + 1) ≤ (x + 1) / 2022 := h6
      have h24 : 2022 / (x + 1) ≤ (min (min (min (x / 2022) (2022 / (x - 1))) (2022 / x)) ((x + 1) / 2022)) := by
        simp [min_le_iff, h20, h21, h22, h23]
      linarith
    have h12 : min (min (min (min (x / 2022) (2022 / (x - 1))) (2022 / x)) ((x + 1) / 2022)) (2022 / (x + 1)) = 2022 / (x + 1) := by
      rw [min_eq_right h19]
    linarith
  exact h7