import Mathlib

theorem algebra_207788 :
    IsLeast {z : ℝ | ∃ x y, z = Real.cos (x + y) ∧ Real.cos x + Real.cos y = 1 / 3} (-17 / 18) := by
  constructor
  · -- Prove -17/18 is in the set
    use Real.arccos (1 / 6), Real.arccos (1 / 6)
    constructor
    · -- Show z = cos(x + y)
      have hcos : Real.cos (Real.arccos (1 / 6) + Real.arccos (1 / 6)) =
          Real.cos (Real.arccos (1 / 6)) * Real.cos (Real.arccos (1 / 6)) - Real.sin (Real.arccos (1 / 6)) * Real.sin (Real.arccos (1 / 6)) := by
        rw [Real.cos_add]
      rw [hcos]
      have h1 : Real.cos (Real.arccos (1 / 6)) = 1 / 6 := Real.cos_arccos (by norm_num) (by norm_num)
      have h2 : Real.sin (Real.arccos (1 / 6)) = Real.sqrt 35 / 6 := by
        have h3 : Real.sin (Real.arccos (1 / 6)) = Real.sqrt (1 - (1 / 6) ^ 2) := by
          rw [Real.sin_arccos]
        rw [h3]
        have h4 : Real.sqrt (1 - (1 / 6 : ℝ) ^ 2) = Real.sqrt (35 / 36 : ℝ) := by norm_num
        rw [h4]
        have h5 : Real.sqrt (35 / 36 : ℝ) = Real.sqrt 35 / 6 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h5]
        all_goals norm_num
      rw [h1, h2]
      have h6 : (Real.sqrt 35 : ℝ) ^ 2 = 35 := by
        rw [Real.sq_sqrt]
        norm_num
      nlinarith [h6]
    · -- Show cos x + cos y = 1/3
      have h1 : Real.cos (Real.arccos (1 / 6)) = 1 / 6 := Real.cos_arccos (by norm_num) (by norm_num)
      linarith [h1]
  · -- Prove -17/18 is a lower bound
    intro z hz
    rcases hz with ⟨x, y, hzy, hcosxy⟩
    have hcos : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
      rw [Real.cos_add]
    rw [hcos] at hzy
    nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin x - Real.sin y),
      Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y,
      sq_nonneg (Real.cos x - 1 / 6), sq_nonneg (Real.cos y - 1 / 6),
      hcosxy, Real.sin_sq_le_one x, Real.sin_sq_le_one y,
      Real.cos_le_one x, Real.cos_le_one y]