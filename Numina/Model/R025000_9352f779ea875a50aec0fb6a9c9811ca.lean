import Mathlib

theorem algebra_181773 {p q : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q)
    (hroots : ∃ x y, x ≠ y ∧ f x = 0 ∧ f y = 0 ∧ x = 2 * y) :
    p = -15 → q = 50 := by
  intro hp
  rcases hroots with ⟨x, y, hxy, hx, hy, hx2y⟩
  have h1 : x ^ 2 + p * x + q = 0 := by
    rw [hf] at hx
    simpa using hx
  have h2 : y ^ 2 + p * y + q = 0 := by
    rw [hf] at hy
    simpa using hy
  have eq1 : x ^ 2 + p * x + q = 0 := by linarith
  have eq2 : y ^ 2 + p * y + q = 0 := by linarith
  have eq3 : (x - y) * (x + y + p) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · -- x - y = 0 means x = y, a contradiction
    exfalso
    apply hxy
    linarith
  · -- x + y + p = 0, as desired
    have h3 : x = 2 * y := hx2y
    have h4 : 3 * y + p = 0 := by
      have eq5 : x + y + p = 0 := by linarith
      rw [show x = 2 * y by linarith] at eq5
      linarith
    have h5 : y = 5 := by
      rw [show p = -15 by linarith [hp]] at h4
      linarith
    have h6 : q = 50 := by
      rw [show y = 5 by linarith [h5], show p = -15 by linarith [hp]] at eq2
      nlinarith
    linarith [h6]