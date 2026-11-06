import Mathlib

theorem algebra_279061 {ρ1 ρ2 : ℝ} (hρ1 : ρ1 ≠ 0) (hρ2 : ρ2 ≠ 0)
    (hvol : (1 / 0.8) * ρ1 = ρ2) :
    ρ2 / ρ1 = 1.25 := by
  have h1 : ρ2 / ρ1 = 1 / (0.8 : ℝ) := by
    field_simp [hρ1]
    linarith
  rw [h1]
  norm_num