import Mathlib
theorem algebra_19726 {f g : ℝ → ℝ} (hf : ∀ x, f x = g (g x) - g x) (hg : ∀ x, g x = 2 * x - 1) :
    f 3 = 4 := by
  have h1 : f 3 = g (g 3) - g 3 := by
    apply hf
  have h2 : g 3 = 5 := by
    rw [hg]
    norm_num
  have h3 : g (g 3) = 9 := by
    rw [show g 3 = 5 by exact h2]
    rw [hg]
    norm_num
  rw [h1]
  rw [h3, h2]
  all_goals norm_num