import Mathlib

open Real

theorem inequalities_303 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    3 / 10 ≥ 1 / (a ^ 2 + 9) + 1 / (b ^ 2 + 9) + 1 / (c ^ 2 + 9) := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h10 : a + b + c = 3 := h
  have h11 : 1 / (a ^ 2 + 9) ≤ (6 - a) / 50 := by
    have h11 : 0 < a ^ 2 + 9 := by nlinarith
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a - 1)]
  have h12 : 1 / (b ^ 2 + 9) ≤ (6 - b) / 50 := by
    have h12 : 0 < b ^ 2 + 9 := by nlinarith
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b - 1)]
  have h13 : 1 / (c ^ 2 + 9) ≤ (6 - c) / 50 := by
    have h13 : 0 < c ^ 2 + 9 := by nlinarith
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c - 1)]
  have h14 : 1 / (a ^ 2 + 9) + 1 / (b ^ 2 + 9) + 1 / (c ^ 2 + 9) ≤ 3 / 10 := by
    have h11' : 1 / (a ^ 2 + 9) ≤ (6 - a) / 50 := h11
    have h12' : 1 / (b ^ 2 + 9) ≤ (6 - b) / 50 := h12
    have h13' : 1 / (c ^ 2 + 9) ≤ (6 - c) / 50 := h13
    have h14 : 1 / (a ^ 2 + 9) + 1 / (b ^ 2 + 9) + 1 / (c ^ 2 + 9) ≤ ( (6 - a) + (6 - b) + (6 - c) ) / 50 := by
      linarith [h11', h12', h13']
    have h15 : ( (6 - a) + (6 - b) + (6 - c) ) / 50 = 3 / 10 := by
      have h16 : (6 - a) + (6 - b) + (6 - c) = 15 := by
        nlinarith [h10]
      rw [h16]
      norm_num
    nlinarith [h14, h15, h10]
  linarith [h14]