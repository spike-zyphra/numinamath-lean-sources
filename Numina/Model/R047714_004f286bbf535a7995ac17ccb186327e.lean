import Mathlib

theorem inequalities_599017 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) ≤ 1 ∧
    (x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) = 1 ↔ x * y * z = 1) := by

  constructor
  · -- $\le 1$ part.
    have h1 : 0 < (1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x) := by
      positivity
    have h2 : x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) - 1 ≤ 0 := by
      have h3 : x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) - 1 =
          (x * (1 + y + y * z) * (1 + z + z * x) + y * (1 + x + x * y) * (1 + z + z * x) + z * (1 + x + x * y) * (1 + y + y * z) - (1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x)) / ((1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x)) := by
        field_simp
        <;> ring
      rw [h3] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
                  sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
                  sq_nonneg (x * y * z - 1), 
                  mul_pos hx hy, 
                  mul_pos hx hz, 
                  mul_pos hy hz
                 ]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith
  · -- Equality holds if and only if $x * y * z = 1$
    constructor
    · -- Assume that $\sum_{cyc} \frac{x}{1 + x + x * y} = 1$, prove that $x * y * z = 1$
      intro heq
      have h1 : 0 < (1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x) := by
        positivity
      have h3 : x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) - 1 = 
          (x * (1 + y + y * z) * (1 + z + z * x) + y * (1 + x + x * y) * (1 + z + z * x) + z * (1 + x + x * y) * (1 + y + y * z) - (1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x)) / ((1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x)) := by 
        field_simp
        <;> ring
      have h4 : x * (1 + y + y * z) * (1 + z + z * x) + y * (1 + x + x * y) * (1 + z + z * x) + z * (1 + x + x * y) * (1 + y + y * z) - (1 + x + x * y) * (1 + y + y * z) * (1 + z + z * x) = 0 := by
        have h5 : (x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) - 1) = 0 := by
          linarith [heq]
        rw [h3] at h5
        field_simp at h5 ⊢
        <;> nlinarith [h1]
      have h8 : x * y * z = 1 := by
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
                  sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
                  sq_nonneg (x * y * z - 1), 
                  mul_pos hx hy, 
                  mul_pos hx hz, 
                  mul_pos hy hz
                 ]
      linarith [h8]
    · -- Assume that $x * y * z = 1$, prove that $\sum_{cyc} \frac{x}{1 + x + x * y} = 1$
      intro heq
      have h1 : x * y * z = 1 := by
        linarith [heq]
      have h4 : x / (1 + x + x * y) + y / (1 + y + y * z) + z / (1 + z + z * x) = 1 := by
        field_simp [(show 1 + x + x * y ≠ 0 by positivity), 
                    (show 1 + y + y * z ≠ 0 by positivity), 
                    (show 1 + z + z * x ≠ 0 by positivity)
                   ]
        <;> nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
                      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
                      sq_nonneg (x * y * z - 1), 
                      mul_pos hx hy, 
                      mul_pos hx hz, 
                      mul_pos hy hz, 
                      h1
                     ]
      linarith [h4]