import Mathlib

theorem algebra_154124 (x y z : ℝ) (h₀ : 8 * x - y - 3 * z - 1 = 0) (h₁ : x + y + z + 10 = 0) :
    (x + 1) / 2 = (y + 9) / (-11 : ℝ) ∧ (y + 9) / (-11 : ℝ) = z / 9 := by
  have h2 : y = -x - z - 10 := by linarith
  rw [h2] at h₀
  have hx : x = (2 * z - 9) / 9 := by
    linarith
  have h_eq1 : (x + 1) / 2 = z / 9 := by
    rw [show x + 1 = (2 * z) / 9 by
      linarith [hx]
    ]
    ring_nf
    <;> linarith
  have hy : y + 9 = (-11 * z) / 9 := by
    have h3 : x = (2 * z - 9) / 9 := hx
    have h4 : y = -x - z - 10 := h2
    rw [h4]
    rw [h3]
    linarith [h₀, h₁, hx]
  have h_eq2 : (y + 9) / (-11 : ℝ) = z / 9 := by
    rw [show (y + 9 : ℝ) = (-11 * z) / 9 by
      linarith [hy]
    ]
    ring_nf
  constructor
  · -- Transitivity to connect (x+1)/2 with (y+9)/(-11)
    linarith [h_eq1, h_eq2]
  · -- Direct from h_eq2
    linarith [h_eq2]