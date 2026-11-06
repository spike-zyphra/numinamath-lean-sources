import Mathlib

theorem algebra_167387 {f g : ℝ → ℝ} (hfg : ∀ x y, f (x + y) + f (x - y) = 2 * f x * g x)
    (hf : ∀ x, f x ≠ 0) (hfg' : ∀ x, |f x| ≤ 1) : ∀ y, |g y| ≤ 1 := by
  have h1 : ∀ x, g x = 1 := by
    intro x
    have h2 := hfg x 0
    have eq1 : f (x + (0 : ℝ)) + f (x - (0 : ℝ)) = 2 * f x * g x := by
      simpa using h2
    have eq2 : f (x + (0 : ℝ)) = f x := by
      simp
    have eq3 : f (x - (0 : ℝ)) = f x := by
      simp
    rw [eq2, eq3] at eq1
    have h3 : f x ≠ 0 := hf x
    have eq5 : g x = 1 := by
      apply (mul_left_inj' h3).mp
      linarith
    exact eq5
  intro y
  have hy : g y = 1 := h1 y
  rw [hy]
  norm_num