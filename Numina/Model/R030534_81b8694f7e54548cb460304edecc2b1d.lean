import Mathlib

open Real

theorem algebra_96851 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x + b)
    (hinv : ∀ x, f (b * x + a) = x) : a + b = -2 := by 
  have eq1 := hinv 0
  simp [hf] at eq1
  have eq2 := hinv 1
  simp [hf] at eq2
  have eq3 : a ^ 2 + b = 0 := by
    nlinarith 
  have eq4 : a * b + a ^ 2 + b = 1 := by
    nlinarith 
  have eq5 : b = -a ^ 2 := by 
    linarith 
  rw [eq5] at eq4 
  have eq6 : a ^ 3 = -1 := by 
    nlinarith 
  have eq7 : a = -1 := by 
    have h1 : a ^ 3 + 1 = 0 := by 
      linarith 
    have h2 : (a + 1) * (a ^ 2 - a + 1) = 0 := by 
      linarith 
    cases' (mul_eq_zero.1 h2) with h3 h4 
    · -- a + 1 = 0 
      linarith 
    · -- a ^ 2 - a + 1 = 0 
      nlinarith [sq_nonneg (a - 1 / 2)]
  have eq8 : b = -1 := by 
    rw [eq7] at eq5 
    nlinarith 
  linarith [eq7, eq8]