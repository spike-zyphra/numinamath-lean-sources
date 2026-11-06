import Mathlib

theorem algebra_4097 :
    IsLeast {u : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ u = (x + y) / (x * y * z)} 16 := by 
  constructor
  · -- Show 16 is in the set
    use 1 / 4, 1 / 4, 1 / 2
    norm_num
  · -- Show 16 is minimal
    intro u hu
    rcases hu with ⟨x, y, z, hx, hy, hz, heq1, heq2⟩
    have h1 : x + y + z = 1 := by linarith
    have h2 : x * y * z > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h3 : x + y ≥ 16 * (x * y * z) := by
      have hz_eq : z = 1 - (x + y) := by linarith
      rw [hz_eq]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1 / 2), sq_nonneg (x - 1 / 4), sq_nonneg (y - 1 / 4)]
    have h4 : (x + y) / (x * y * z) ≥ 16 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have h_eq : u = (x + y) / (x * y * z) := heq2
    linarith [h_eq, h4]