import Mathlib

theorem algebra_133142 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * (b + c) + b * (c + a) + c * (a + b) = a * b + b * c + c * a) :
    ∃ k : ℤ, (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)) / (a * b * c) = k := by
  have h1 : a * b + b * c + c * a = 0 := by 
    linarith
  have h2 : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) = -3 * (a * b * c) := by 
    have eq1 : a * b + b * c + c * a = 0 := h1
    have eq2 : (a + b) * (b + c) * (c + a) = - a * b * c := by
      have h3 : (a + b) * (b + c) * (c + a) = (a + b + c) * (a * b + b * c + c * a) - a * b * c := by 
        ring
      rw [h3]
      rw [eq1]
      all_goals linarith
    have eq3 : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) + 3 * (a * b * c) = 0 := by
      have eq4 : (a + b) * (b + c) * (c + a) = -a * b * c := eq2
      have eq5 : (a + b) * (b + c) * (c + a) = a ^ 2 * b + a ^ 2 * c + a * b ^ 2 + b ^ 2 * c + a * c ^ 2 + b * c ^ 2 + 2 * (a * b * c) := by
        ring
      linarith [eq4, eq5]
    linarith
  use -3
  field_simp [ha, hb, hc, show a * b * c ≠ 0 by 
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
  ]
  <;> rw [h2]
  <;> norm_num
  all_goals linarith