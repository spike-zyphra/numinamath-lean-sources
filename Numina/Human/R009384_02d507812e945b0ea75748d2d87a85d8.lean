import Mathlib
/-If f(x)=g(g(x))-g(x) and g(x)=2x-1, find f(3).-/
theorem algebra_19726 {f g : ℝ → ℝ} (hf : ∀ x, f x = g (g x) - g x) (hg : ∀ x, g x = 2 * x - 1) :
    f 3 = 4 := by
  rw [hf _] -- f (3) = g (g (3)) - g (3)
  have := hg 3 
  norm_num at this -- g (3) = 2 * 3 - 1 = 5
  rw [this, hg _]
  norm_num -- f (3) = g (g (3)) - g (3) = g (5) - 5 = 2 * 5 - 1 - 5 = 4