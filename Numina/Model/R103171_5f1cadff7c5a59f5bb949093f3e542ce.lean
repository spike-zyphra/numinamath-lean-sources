import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_302228 : IsGreatest {x | ∃ t : ℝ, x = cos (2*t) + 2*abs (sin t)} (3/2) := by
  constructor
  · -- Show it's attained in the set
    use Real.pi / 6
    have hsin : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have hcos : cos (2 * (Real.pi / 6)) = 1 / 2 := by
      have h1 : 2 * (Real.pi / 6) = Real.pi / 3 := by ring
      rw [h1]
      exact Real.cos_pi_div_three
    rw [hcos, hsin]
    norm_num [abs_of_nonneg]
  · -- Show it's the greatest in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : -1 ≤ sin t ∧ sin t ≤ 1 := by 
      constructor 
      · linarith [Real.neg_one_le_sin t]
      · linarith [Real.sin_le_one t]
    have ht' : x = 1 - 2 * (sin t)^2 + 2 * abs (sin t) := by 
      rw [ht]
      have h : cos (2 * t) = 1 - 2 * (sin t)^2 := by
        rw [cos_two_mul]
        rw [sin_sq]
        <;> ring
      rw [h]
      <;> ring
    rw [ht']
    by_cases h2 : sin t ≥ 0 
    · -- When $\sin t ≥ 0$, we have $|\sin t| = \sin t$
      rw [abs_of_nonneg h2]
      nlinarith [sq_nonneg (sin t - 1 / 2), sq_nonneg (sin t + 1 / 2), h1.1, h1.2]
    · -- When $\sin t < 0$, we have $|\sin t| = -\sin t$
      rw [abs_of_neg (lt_of_not_ge h2)]
      nlinarith [sq_nonneg (sin t + 1 / 2), sq_nonneg (sin t - 1 / 2), h1.1, h1.2]