import Mathlib

theorem algebra_99164 {a b c : ℝ} (h : a + b + c = 0) (h1 : a ≠ 0) (h2 : b ≠ 0) (h3 : c ≠ 0) :
    a^2 / (b * c) + b^2 / (a * c) + c^2 / (a * b) = 3 := by 
  have h4 : a + b + c = 0 := h
  have h5 : a^3 + b^3 + c^3 = 3 * a * b * c := by
    have h5 : a + b + c = 0 := h
    have h6 : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by
      have : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a*b - a*c - b*c) := by
        ring
      rw [this, h5]
      norm_num
    linarith
  have eq2 : a^2 / (b * c) + b^2 / (a * c) + c^2 / (a * b) = (a^3 + b^3 + c^3) / (a * b * c) := by
    field_simp [h1, h2, h3, show b * c ≠ 0 by
      apply mul_ne_zero
      exact h2
      exact h3
      , show a * c ≠ 0 by
      apply mul_ne_zero
      exact h1
      exact h3
      , show a * b ≠ 0 by
      apply mul_ne_zero
      exact h1
      exact h2
    ]
    ring
  rw [eq2]
  rw [h5]
  field_simp [h1, h2, h3, show a * b * c ≠ 0 by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h1
    exact h2
    exact h3
  ]
  <;> ring_nf <;> norm_num