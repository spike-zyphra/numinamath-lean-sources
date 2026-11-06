import Mathlib

theorem algebra_283543 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x / y = (x + 2) / (y + 7)) :
    x / y = (x + 3) / (y + 10.5) := by
  have h1 : x * (y + 7) = y * (x + 2) := by
    field_simp [hy, show 0 < y + 7 by
      nlinarith] at h
    linarith
  have h2 : 7 * x = 2 * y := by
    nlinarith [h1]
  have eq1 : x * (y + 10.5) = y * (x + 3) := by
    have h4 : 10.5 * x = 3 * y := by
      have h5 : y = (7 / 2) * x := by
        nlinarith [h2]
      rw [h5]
      ring_nf
      <;> nlinarith
    ring_nf at h4 ⊢
    linarith [h4
    ]
  field_simp [hy, show 0 < y + 10.5 by
    nlinarith]
  <;> nlinarith [eq1]