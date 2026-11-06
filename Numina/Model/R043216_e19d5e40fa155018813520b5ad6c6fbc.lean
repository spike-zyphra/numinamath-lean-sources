import Mathlib

theorem algebra_250942 :
    {x : ℝ | 3.5/(x+2) + 3.5/(x-2) = 5/3 ∧ x > 2} = {5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x satisfies the equation and x > 2, prove x = 5
    intro h
    rcases h with ⟨h1, h2⟩
    have eq1 : x + 2 ≠ 0 := by linarith
    have eq2 : x - 2 ≠ 0 := by linarith
    field_simp [(show x + 2 ≠ 0 by linarith), (show x - 2 ≠ 0 by linarith)] at h1
    ring_nf at h1
    have h3 : (x - 5) * (x + 0.8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- x - 5 = 0
      linarith
    · -- x + 0.8 = 0
      norm_num at h5
      nlinarith
  · -- Assume x = 5, prove it satisfies the equation and x > 2
    intro h
    rw [h]
    constructor
    · -- Check equation
      norm_num
    · -- Check x > 2
      norm_num