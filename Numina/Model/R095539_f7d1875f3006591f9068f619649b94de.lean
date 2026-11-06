import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_305328 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : b + c ≤ 2 * a) (h2 : a + c ≤ 2 * b) :
  (1 / 2) < b / a ∧ b / a < 2 := by
  have h3 : b < 2 * a := by linarith [h1, hc]
  have h4 : a < 2 * b := by linarith [h2, hc]

  have h5 : b / a < 2 := by
    have h6 : 0 < a := ha
    have h7 : b < 2 * a := h3
    have h8 : b / a < (2 * a) / a := by apply (div_lt_div_right h6).mpr h7
    have h9 : (2 * a) / a = 2 := by
      field_simp
      <;> linarith
    linarith [h8, h9]

  have h10 : 1 / 2 < b / a := by
    have h11 : 0 < a := ha
    have h12 : a < 2 * b := h4
    have h13 : a / a < (2 * b) / a := by
      apply (div_lt_div_right h11).mpr h12
    have h14 : a / a = 1 := by
      field_simp
      <;> linarith
    have h15 : (2 * b) / a = 2 * (b / a) := by
      field_simp
      <;> linarith
    have h16 : 1 < 2 * (b / a) := by
      linarith [h13, h14, h15]
    linarith
  
  exact ⟨h10, h5⟩