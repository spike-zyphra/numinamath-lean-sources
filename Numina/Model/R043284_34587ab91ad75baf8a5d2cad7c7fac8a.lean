import Mathlib

theorem algebra_326884 {f : ℝ → ℝ} (h : ∀ x y, f x * f y = f (2 * x * y + 3) + 3 * f (x + y) - 3 * f x + 6 * x) :
    ∀ x, f x = 2 * x + 3 := by 
  have eqA : ∀ x : ℝ, f x * f 0 = f 3 + 6 * x := by 
    intro x 
    specialize h x 0 
    simp at h 
    linarith 
  have eq1 := eqA 0
  have eq2 := eqA 3
  have eq3 : f 0 ^ 2 = f 3 := by 
    nlinarith 
  have eq4 : f 3 * (f 0 - 1) = 18 := by
    nlinarith 
  have eq5 : f 0 = 3 := by
    have h1 : f 0 ^ 3 - f 0 ^ 2 - 18 = 0 := by
      rw [show f 3 = f 0 ^ 2 by linarith [eq3]] at eq4 
      nlinarith 
    have h2 : (f 0 - 3) * (f 0 ^ 2 + 2 * f 0 + 6) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · linarith 
    · -- f 0 ^ 2 + 2 * f 0 + 6 = 0 has no real roots 
      nlinarith [sq_nonneg (f 0 + 1)]
  have eq6 : f 3 = 9 := by 
    rw [eq5] at eq3 
    nlinarith 
  intro x 
  have eq7 := eqA x 
  rw [eq5] at eq7 
  rw [eq6] at eq7 
  have eq8 : f x = 2 * x + 3 := by 
    nlinarith 
  linarith