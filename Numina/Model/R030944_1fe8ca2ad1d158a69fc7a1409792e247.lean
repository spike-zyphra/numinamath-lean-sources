import Mathlib

theorem algebra_157507 {f g : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (hg : ∀ x, g (-x) = g x)
    (hfg : ∀ x, f x - g x = x ^ 2 + 9 * x + 12) :
    ∀ x, f x + g x = -x ^ 2 + 9 * x - 12 := by
  intro x
  have eq1 := hfg x
  have eq2 := hfg (-x)
  have eq3 : f (-x) = -f x := hf x
  have eq4 : g (-x) = g x := hg x
  rw [eq3, eq4] at eq2
  have eq5 : g x = -x ^ 2 - 12 := by
    nlinarith
  have eq6 : f x = 9 * x := by
    linarith [eq1, eq5]
  rw [eq6, eq5]
  ring