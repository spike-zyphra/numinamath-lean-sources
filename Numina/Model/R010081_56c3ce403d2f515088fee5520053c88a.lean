import Mathlib

theorem algebra_15180 :
    {t : ℝ | t ≥ 0 ∧ -4.9 * t ^ 2 + 3.5 * t + 5 = 0} = {10 / 7} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume t is in the set on the left, meaning t ≥ 0 and -4.9*t^2 + 3.5*t + 5 = 0
    rintro ⟨ht, heq⟩
    have h1 : -4.9 * t ^ 2 + 3.5 * t + 5 = 0 := heq
    have h2 : 49 * t^2 - 35 * t - 50 = 0 := by
      ring_nf at h1 ⊢
      nlinarith
    have h3 : (t - 10/7) * (49 * t + 35) = 0 := by
      nlinarith [h2]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- case where t - 10/7 = 0
      linarith
    · -- case where 49t + 35 = 0
      have ht2 : t < 0 := by
        nlinarith
      linarith
  · -- Assume t = 10/7
    intro ht
    rw [ht]
    constructor
    · -- Show that 10/7 ≥ 0
      norm_num
    · -- Show that -4.9 * (10/7)^2 + 3.5 * (10/7) + 5 = 0
      norm_num