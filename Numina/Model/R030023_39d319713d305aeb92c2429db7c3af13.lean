import Mathlib

theorem algebra_251881 :
    {t : ℝ | 343 = 3*t + (5*t^2)/2 + 4*t + (7*t^2)/2 ∧ t > 0} = {7} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume t ≥ 0 and satisfies the equation
    intro h
    rcases h with ⟨h_eq, ht⟩
    have h_eq' : 6 * t^2 + 7 * t - 343 = 0 := by
      linarith
    have h_eq2 : (t - 7) * (6 * t + 49) = 0 := by
      linarith [h_eq']
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    · -- $t - 7 = 0$, so $t = 7$.
      linarith
    · -- $6 * t + 49 = 0$, which means $t < 0$.
      nlinarith
  · -- Show that 7 satisfies the equation
    intro h
    rw [h]
    constructor
    · -- Verify that 7 satisfies the equation
      norm_num
    · -- Verify that 7 > 0
      norm_num
  all_goals linarith