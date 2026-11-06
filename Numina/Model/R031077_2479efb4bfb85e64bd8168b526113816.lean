import Mathlib

theorem algebra_306038 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + b^2 + c^2 = 1) (h2 : a * (1 / b + 1 / c) + b * (1 / c + 1 / a) +
    c * (1 / a + 1 / b) = -3) :
    a + b + c = 1 ∨ a + b + c = -1 ∨ a + b + c = 0 := by

  have eq1 : a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) = 
    (a * (b + c) ) / (b * c) + (b * (a + c) ) / (a * c) + (c * (a + b) ) / (a * b) := by 
    field_simp [hb, hc, ha]
    <;> ring

  have eq2 : (a * (b + c) ) / (b * c) + (b * (a + c) ) / (a * c) + (c * (a + b) ) / (a * b) = -3 := by 
    linarith [h2, eq1]

  have eq3 : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) + 3 * a * b * c = 0 := by
    have h3 : a * b * c ≠ 0 := by
      apply mul_ne_zero 
      apply mul_ne_zero 
      exact ha 
      exact hb 
      exact hc 
    have eq4 : (a * (b + c) ) / (b * c) + (b * (a + c) ) / (a * c) + (c * (a + b) ) / (a * b) = 
      ( a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ) / (a * b * c) := by
      field_simp [hb, hc, ha, show b * c ≠ 0 by
        apply mul_ne_zero hb hc, show a * c ≠ 0 by
          apply mul_ne_zero ha hc, show a * b ≠ 0 by
            apply mul_ne_zero ha hb ]
      ring 
    rw [eq4] at eq2
    field_simp [h3] at eq2 ⊢ 
    nlinarith 

  have eq4 : (a + b + c) * (a * b + b * c + c * a) = 0 := by 
    nlinarith [eq3]

  cases (mul_eq_zero.mp eq4) with
  | inl h3 =>
    right 
    right 
    linarith 
  | inr h4 =>
    have h5 : (a + b + c)^2 = 1 := by 
      nlinarith [h1, h4]

    have h6 : a + b + c = 1 ∨ a + b + c = -1 := by 
      have h : (a + b + c) ^ 2 = 1 := h5 
      have : a + b + c = 1 ∨ a + b + c = -1 := by 
        rw [sq_eq_one_iff] at h 
        tauto 
      assumption

    cases h6 with
    | inl h7 =>
      left 
      linarith
    | inr h8 =>
      right 
      left 
      linarith