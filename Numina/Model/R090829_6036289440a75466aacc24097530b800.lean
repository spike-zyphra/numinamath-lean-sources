import Mathlib

theorem algebra_180943 (x : ℝ) (hx : x ∈ Set.Icc (-1) 3) :
    Real.sqrt (x + 1) + Real.sqrt (3 - x) ≠ 17 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.sqrt (x + 1) ≤ 2 := by
    have h2 : x + 1 ≤ 4 := by linarith
    have h3 : Real.sqrt (x + 1) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith
  have h5 : Real.sqrt (3 - x) ≤ 2 := by
    have h6 : 3 - x ≤ 4 := by linarith
    have h7 : Real.sqrt (3 - x) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    have h8 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith
  have h9 : Real.sqrt (x + 1) + Real.sqrt (3 - x) ≤ 4 := by linarith
  intro h
  linarith [h9, h]