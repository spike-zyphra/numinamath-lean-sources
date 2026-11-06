import Mathlib

theorem algebra_143572 (d l : ℝ) (h₀ : d > 0) (h₁ : l > 0)
    (h₂ : 73.5 = (π * d ^ 2 * l) / (86 * 10 ^ 3)) :
    147 = (π * (2 * d) ^ 2 * (l / 2)) / (86 * 10 ^ 3) := by
  have h3 : (π * (2 * d) ^ 2 * (l / 2)) / (86 * 10 ^ 3) = 2 * ((π * d ^ 2 * l) / (86 * 10 ^ 3)) := by
    ring_nf
    <;> field_simp <;> ring
  have h4 : 2 * ((π * d ^ 2 * l) / (86 * 10 ^ 3)) = 2 * 73.5 := by
    rw [h₂]
  rw [h3, h4]
  all_goals norm_num