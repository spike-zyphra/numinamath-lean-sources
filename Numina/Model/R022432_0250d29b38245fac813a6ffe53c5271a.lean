import Mathlib

theorem algebra_126360 {f g : ℤ → ℤ} (hf : f = fun x => x^2 + 4 * x + 3)
    (hg : g = fun x => x^2 + 2 * x - 1) :
    ∀ x, f (g (f x)) = g (f (g x)) ↔ x = -2 := by 
  intro x
  constructor
  · -- Assume f (g (f x)) = g (f (g x)), prove x = -2.
    intro h_eq
    simp only [hf, hg] at h_eq
    have h1 : x = -2 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (x^2 + 4 * x + 3 - (x^2 + 2 * x - 1)), sq_nonneg ((x^2 + 4 * x + 3) - (x^2 + 2 * x - 1)), sq_nonneg (x^2 + 4 * x + 3 + x^2 + 2 * x - 1), sq_nonneg (x^2 + 4 * x + 3 - (x^2 + 2 * x - 1)), sq_nonneg (x + 2)]
    exact h1
  · -- Assume x = -2, prove f (g (f x)) = g (f (g x)).
    intro h_eq
    rw [h_eq]
    simp only [hf, hg]
    all_goals norm_num