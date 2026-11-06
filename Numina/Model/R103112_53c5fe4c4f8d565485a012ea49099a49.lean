import Mathlib

theorem algebra_297018 (a b : ℝ) (ha : 0 ≤ a) (hb : 3 * Real.sqrt a + 5 * abs b = 7) :
    2 * Real.sqrt a - 3 * abs b ∈ Set.Icc (-21 / 5) (14 / 3) := by 
  have h1 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h2 : Real.sqrt a ≤ 7 / 3 := by
    have h3 : 5 * abs b ≥ 0 := by positivity
    have h4 : 3 * Real.sqrt a ≤ 7 := by linarith
    nlinarith [Real.sqrt_nonneg a, abs_nonneg b]
  have h5 : abs b = (7 - 3 * Real.sqrt a) / 5 := by 
    have h6 : 3 * Real.sqrt a + 5 * abs b = 7 := by linarith
    linarith
  have hs1 : 2 * Real.sqrt a - 3 * abs b = (19 * Real.sqrt a - 21) / 5 := by 
    rw [h5]
    linarith
  rw [hs1]
  constructor
  · -- Show that -21/5 ≤ (19 * sqrt a - 21) / 5
    have h7 : 0 ≤ Real.sqrt a := by positivity
    linarith [h7]
  · -- Show that (19 * sqrt a - 21) / 5 ≤ 14/3
    have h8 : Real.sqrt a ≤ 7 / 3 := h2
    linarith [h8]