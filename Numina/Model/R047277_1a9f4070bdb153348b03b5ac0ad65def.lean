import Mathlib

theorem algebra_298168 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 - 2 * x + 2)
    (g : ℝ → ℝ) (hg : g = fun x => -x^2 + a * x + b) (P : ℝ) (hP : f P = g P)
    (hP' : deriv f P * deriv g P = -1) :
    a + b = 5 / 2 := by

  have eq1 : P ^ 2 - 2 * P + 2 = -P ^ 2 + a * P + b := by
    have hk1 : f P = P ^ 2 - 2 * P + 2 := by 
      rw [hf]
    have hk2 : g P = -P ^ 2 + a * P + b := by 
      rw [hg]
    rw [hk1, hk2] at hP
    all_goals linarith

  have eq2 : deriv f P = 2 * P - 2 := by
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_id'', mul_comm]

  have eq3 : deriv g P = -2 * P + a := by
    rw [hg]
    simp [deriv_pow, deriv_add, deriv_mul, deriv_id'', mul_comm a, mul_assoc]
    <;> field_simp <;> ring_nf

  rw [eq2, eq3] at hP'

  have eq4 : (2 * P - 2) * (-2 * P + a) = -1 := by 
    linarith

  have eq5 : 2 * P ^ 2 - (2 + a) * P + (2 - b) = 0 := by
    linarith [eq1]

  have eq6 : -4 * P ^ 2 + 2 * a * P + 4 * P - 2 * a + 1 = 0 := by 
    nlinarith [eq4]

  nlinarith [sq_nonneg (P - 1), sq_nonneg (2 * P - 2), eq5, eq6]