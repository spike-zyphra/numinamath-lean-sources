import Mathlib

theorem algebra_215818 {f g : ℝ → ℝ} (hf : ∃ a b, f = fun x => x^2 + a * x + b)
    (hg : ∃ c d, g = fun x => x^2 + c * x + d) (hfg : f ≠ g) (hfg1 : f 19 + f 92 = g 19 + g 92) :
    ∃ x, f x = g x ∧ x = 55 + 1 / 2 := by
  rcases hf with ⟨a, b, hf⟩
  rcases hg with ⟨c, d, hg⟩
  have eq1 : f 19 + f 92 = g 19 + g 92 := hfg1
  simp [hf, hg] at eq1
  have eq2 : 111 * (a - c) = 2 * (d - b) := by 
    linarith
  use 55 + 1 / 2
  constructor
  · -- Show that $f(55 + \frac{1}{2}) = g(55 + \frac{1}{2})$
    simp [hf, hg]
    ring_nf at eq1 eq2 ⊢
    all_goals 
      linarith [eq2, eq1]
  · -- Show that x = 55 + 1/2
    rfl