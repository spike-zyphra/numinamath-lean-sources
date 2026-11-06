import Mathlib

open Real Set

theorem inequalities_322955 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ Icc 1 4, a * x + b - 3 ≤ 0) :
    1 / a - b ≥ 1 := by
  have h1 := h 1 (left_mem_Icc.mpr (by norm_num))
  have h2 := h 4 (right_mem_Icc.mpr (by norm_num))
  have h3 : a + b ≤ 3 := by linarith
  have h4 : 4 * a + b ≤ 3 := by linarith
  have h8 : b ≤ 3 - 4 * a := by linarith
  have h9 : 1 / a - b ≥ 1 / a - (3 - 4 * a) := by nlinarith
  have h10 : 1 / a - (3 - 4 * a) ≥ 1 := by
    have h11 : 1 / a + 4 * a ≥ 4 := by
      have h19 : (2 * a - 1) ^ 2 ≥ 0 := sq_nonneg (2 * a - 1)
      have h20 : 1 / a + 4 * a - 4 ≥ 0 := by 
        have h21 : 1 / a + 4 * a - 4 = (2 * a - 1) ^ 2 / a := by
          field_simp
          <;> nlinarith
        rw [h21]
        apply div_nonneg 
        nlinarith
        positivity
      linarith
    linarith
  linarith [h9, h10]