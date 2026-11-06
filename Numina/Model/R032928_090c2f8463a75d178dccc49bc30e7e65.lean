import Mathlib

theorem inequalities_602003 (x y z : ℝ) (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x) :
    x^2 / (x - y)^2 + y^2 / (y - z)^2 + z^2 / (z - x)^2 ≥ 1 := by

  have h3 : x - y ≠ 0 := by
    intro h
    apply h₀
    linarith

  have h4 : y - z ≠ 0 := by
    intro h
    apply h₁
    linarith

  have h5 : z - x ≠ 0 := by
    intro h
    apply h₂
    linarith

  have h6 : x^2 / (x - y)^2 + y^2 / (y - z)^2 + z^2 / (z - x)^2 - 1 ≥ 0 := by
    have h7 : x^2 / (x - y)^2 + y^2 / (y - z)^2 + z^2 / (z - x)^2 - 1 =
        (x^2 * (y - z)^2 * (z - x)^2 + y^2 * (x - y)^2 * (z - x)^2 + z^2 * (x - y)^2 * (y - z)^2 - (x - y)^2 * (y - z)^2 * (z - x)^2) / ((x - y)^2 * (y - z)^2 * (z - x)^2) := by
      field_simp [show x - y ≠ 0 by exact h3, show y - z ≠ 0 by exact h4, show z - x ≠ 0 by exact h5]
      ring
    rw [h7] at *
    have h8 : x^2 * (y - z)^2 * (z - x)^2 + y^2 * (x - y)^2 * (z - x)^2 + z^2 * (x - y)^2 * (y - z)^2 - (x - y)^2 * (y - z)^2 * (z - x)^2 ≥ 0 := by
      have h10 : x^2 * (y - z)^2 * (z - x)^2 + y^2 * (x - y)^2 * (z - x)^2 + z^2 * (x - y)^2 * (y - z)^2 - (x - y)^2 * (y - z)^2 * (z - x)^2 =
          (x * (y - z) * (z - x) + y * (x - y) * (z - x) + z * (x - y) * (y - z) - (x - y) * (y - z) * (z - x)) ^ 2 := by
        ring
      rw [h10]
      positivity

    have h6543 : (x^2 * (y - z)^2 * (z - x)^2 + y^2 * (x - y)^2 * (z - x)^2 + z^2 * (x - y)^2 * (y - z)^2 - (x - y)^2 * (y - z)^2 * (z - x)^2) / ((x - y)^2 * (y - z)^2 * (z - x)^2) ≥ 0 := by
      apply div_nonneg
      exact h8
      positivity

    exact h6543

  linarith