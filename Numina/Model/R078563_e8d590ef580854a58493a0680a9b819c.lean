import Mathlib

theorem algebra_187679 : IsGreatest {x | ∃ t : ℝ, x = 9 * Real.sin t + 12 * Real.cos t} 15 := by
  constructor
  · -- Show that 15 belongs to the set, i.e., there exists some t such that 9*sin t + 12*cos t = 15.
    use Real.arcsin (3 / 5)
    have h1 : Real.sin (Real.arcsin (3 / 5)) = 3 / 5 := by
      apply Real.sin_arcsin
      all_goals norm_num
    have h2 : Real.cos (Real.arcsin (3 / 5)) = 4 / 5 := by
      have hcos : Real.cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by
        rw [Real.cos_arcsin]
      rw [hcos]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show that 15 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h3 : 9 * Real.sin t + 12 * Real.cos t ≤ 15 := by
      nlinarith [sq_nonneg (Real.sin t - 3 / 5), sq_nonneg (Real.cos t - 4 / 5),
        Real.sin_sq_add_cos_sq t, sq_nonneg (9 * Real.cos t - 12 * Real.sin t)]
    have eq : x = 9 * Real.sin t + 12 * Real.cos t := by
      linarith
    linarith [eq, h3]