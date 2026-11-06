import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_279390 : IsLeast {y | ∃ x : ℝ, x ∈ Ioo 0 Real.pi ∧ y = sin x + 2 / sin x} 3 := by 
  constructor
  · -- We need to find a specific x such that y = 3 is in the set.
    use Real.pi / 2
    constructor
    · -- Show x is in (0, π)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show 3 = sin(π/2) + 2 / sin(π/2)
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      rw [h1]
      norm_num
  · -- We need to show that 3 is a lower bound
    intro y
    rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    have hsin1 : 0 < sin x := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hx1, Real.pi_pos]
      linarith [hx2, Real.pi_pos]
    have hsin2 : sin x ≤ 1 := sin_le_one x
    have h1 : sin x + 2 / sin x - 3 ≥ 0 := by
      have h2 : sin x > 0 := hsin1
      have h3 : sin x + 2 / sin x - 3 = (sin x ^ 2 + 2 - 3 * sin x) / sin x := by
        field_simp
        ring
      rw [h3]
      have h4 : sin x ^ 2 + 2 - 3 * sin x ≥ 0 := by 
        nlinarith [sq_nonneg (sin x - 1), hsin2]
      have h5 : sin x > 0 := hsin1
      apply div_nonneg
      linarith
      all_goals linarith
    linarith