import Mathlib

theorem algebra_12553 {f : ℝ → ℝ} (hf : f = fun x => (x - 2) * x * (x + 1) / 6 + x + 2)
    (a b : ℝ) (ha : f a = b) (hb : f b = 4) : a - b = -2 := by
  have h1 : f b = 4 := hb
  have eq1 : (b - 2) * b * (b + 1) / 6 + b + 2 = 4 := by
    rw [hf] at h1
    exact h1
  have eq3 : (b - 2) * (b ^ 2 + b + 6) = 0 := by
    nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 1/2)]
  cases' (mul_eq_zero.mp eq3) with h2 h3
  · -- b = 2
    have hb2 : b = 2 := by linarith
    have ha2 : f a = 2 := by 
      rw [hb2] at ha 
      linarith
    have eq2 : (a - 2) * a * (a + 1) / 6 + a + 2 = 2 := by 
      rw [hf] at ha2 
      exact ha2 
    have eq4 : a * (a ^ 2 - a + 4) = 0 := by
      field_simp at eq2 ⊢
      nlinarith [sq_nonneg (a), sq_nonneg (a - 2)]
    cases' (mul_eq_zero.mp eq4) with ha1 ha2
    · -- a = 0 
      have ha0 : a = 0 := by linarith
      linarith [hb2, ha0]
    · -- Solving quadratic: no real solution
      exfalso
      nlinarith [sq_nonneg (a - 1/2)]
  · -- Solving cubic: discriminant of quadratic discriminant is negative 
    exfalso
    have h4 : b^2 + b + 6 > 0 := by 
      nlinarith [sq_nonneg (b + 1/2)]
    have h3' : b^2 + b + 6 = 0 := by linarith 
    linarith [h4, h3']