import Mathlib

theorem algebra_867 (t : ℝ) (a b : ℝ)
    (h1 : 0 < t ∧ 0 < a ∧ 0 < b)
    (h2 : a = 6⁻¹)
    (h3 : b = (1 - 0.6) * 6⁻¹)
    (h4 : 10⁻¹ = (1 + 0.2) * b) :
    t = 9 := by
  have hb : b = 0.4 / 6 := by
    rw [h3]
    ring_nf
    <;> norm_num
  rw [hb] at h4
  norm_num at h4
  all_goals linarith [h1.1]