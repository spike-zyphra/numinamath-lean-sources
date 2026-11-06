import Mathlib

theorem algebra_14308 {f g : ℝ → ℝ} (hf : f = fun x => 3 * x - 8)
    (hg : ∀ x, g (f x) = 2 * x ^ 2 + 5 * x - 3) : g (-5) = 4 := by
  have h1 : f 1 = -5 := by 
    rw [hf]
    norm_num
  have h2 := hg 1
  rw [h1] at h2
  norm_num at h2 ⊢
  exact h2