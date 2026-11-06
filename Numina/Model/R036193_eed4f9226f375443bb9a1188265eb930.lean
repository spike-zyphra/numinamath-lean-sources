import Mathlib

theorem algebra_83292 (f : ℝ × ℝ → ℝ)
    (hf1 : ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → f (a, f (b, c)) = c * f (a, b))
    (hf2 : ∀ a : ℝ, a ≠ 0 → f (a, a) = 1)
    (x : ℝ) (hx : x ≠ 0) : 216 = f (x, 36) → x = 7776 := by
  intro h_eq
  have eq1 : ∀ y : ℝ, y ≠ 0 → f (y, 1) = y := by
    intro y hy
    have eq_fyy : f (y, y) = 1 := hf2 y hy
    have eq2 := hf1 y y y hy hy hy
    simp [eq_fyy] at eq2
    simpa using eq2
  have eq2 : f (x, 1) = 7776 := by
    have eq3 : f (x, f (36, 36)) = 36 * f (x, 36) := by
      apply hf1 x 36 36 hx (by norm_num) (by norm_num)
    have eq4 : f (36, 36) = 1 := by
      apply hf2 36 (by norm_num)
    rw [eq4] at eq3
    have eq5 : f (x, 36) = 216 := by linarith [h_eq]
    rw [eq5] at eq3
    linarith
  have eq3 : f (x, 1) = x := by
    specialize eq1 x hx
    simpa using eq1
  rw [eq3] at eq2
  linarith