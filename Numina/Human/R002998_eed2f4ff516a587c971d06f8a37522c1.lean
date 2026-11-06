import Mathlib

theorem algebra_141794 {x y z : ℝ} (h1 : x = 1.2 * y) (h2 : y = 0.8 * z)
    (h3 : x + y + z = 759) :
    x = 264 ∧ y = 220 ∧ z = 275 := by
  have hx : x = 264 := by
    norm_num [h1, h2] at h3
    linarith
  have hy : y = 220 := by
    norm_num [h2] at h3
    linarith
  have hz : z = 275 := by
    norm_num at h3
    linarith
  exact ⟨hx, hy, hz⟩