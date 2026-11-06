import Mathlib

theorem algebra_243817 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : 1 / a + 1 / b + 1 / c + 1 / d = 0) (h2 : a + b + c + d + a * b * c * d = 0) :
    ((1 / (a * b)) - (1 / (c * d))) * (1 / c + 1 / d) = -1 := by
  have eq1 : a * b * c + a * b * d + a * c * d + b * c * d = 0 := by
    field_simp at h1 ⊢ 
    linarith
  have h4 : a + b + c + d = -a * b * c * d := by 
    linarith
  have eq2 : ((1 / (a * b)) - (1 / (c * d))) * (1 / c + 1 / d) = ((c * d - a * b) / (a * b * c * d)) * ((d + c) / (c * d)) := by
    field_simp [ha, hb, hc, hd, show a * b ≠ 0 by
      apply mul_ne_zero
      exact ha
      exact hb, show c * d ≠ 0 by
      apply mul_ne_zero
      exact hc
      exact hd, show a * b * c * d ≠ 0 by
        apply mul_ne_zero
        apply mul_ne_zero
        apply mul_ne_zero
        exact ha
        exact hb
        exact hc
        exact hd] <;> ring_nf <;> field_simp [ha, hb, hc, hd] <;> ring
  rw [eq2]
  have h5 : (c * d - a * b) * (c + d) = - (a * b * c^2 * d^2) := by
    have eq4 : (a * b - c * d) * (c + d) = a * b * c^2 * d^2 := by 
      have eq5 : a * b * (c + d) = - c * d * (a + b) := by 
        nlinarith [eq1]
      calc
        (a * b - c * d) * (c + d) = a * b * (c + d) - c * d * (c + d) := by ring 
        _ = - c * d * (a + b) - c * d * (c + d) := by rw [eq5] 
        _ = - c * d * (a + b + c + d) := by ring 
        _ = - c * d * (- a * b * c * d) := by 
          have h6 : a + b + c + d = - a * b * c * d := by nlinarith [h2, h4]
          rw [h6] 
        _ = a * b * c^2 * d^2 := by
          nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd]
    calc
      (c * d - a * b) * (c + d) = - ((a * b - c * d) * (c + d)) := by ring 
      _ = - (a * b * c^2 * d^2) := by rw [eq4]
  have h6 : a * b * c * d ≠ 0 := by
    apply mul_ne_zero 
    apply mul_ne_zero 
    apply mul_ne_zero
    exact ha 
    exact hb 
    exact hc 
    exact hd
  field_simp [h6, show c * d ≠ 0 by
    apply mul_ne_zero 
    exact hc 
    exact hd, show a * b ≠ 0 by
      apply mul_ne_zero 
      exact ha 
      exact hb
  ]
  <;> nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd, h5, h4, h2, eq1]