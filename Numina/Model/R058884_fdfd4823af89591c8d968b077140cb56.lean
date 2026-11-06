import Mathlib

theorem algebra_170370 {R U : ℝ} (hR : R > 0) (hU : U > 0)
    (hvolmeter : U / (2 * R) = 15 / B) (hammeter : U / (2 * R) = -20) :
    R = 1.5 := by 
  have h2' : 2 * R ≠ 0 := by nlinarith
  have eq3 : U = -20 * (2 * R) := by
    field_simp [h2'] at hammeter
    nlinarith
  rw [eq3] at hU
  have h_neg : -40 * R > 0 := by
    nlinarith
  have contradiction : R < 0 := by
    nlinarith
  linarith