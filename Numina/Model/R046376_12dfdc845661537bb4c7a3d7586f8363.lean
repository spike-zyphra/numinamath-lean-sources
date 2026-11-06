import Mathlib

theorem algebra_249821 : {x : ℝ | 0 ≤ x ∧ Real.sqrt x = x - 2 } = {4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ {x : ℝ | 0 ≤ x ∧ Real.sqrt x = x - 2}, prove x = 4
    rintro ⟨hx1, heq⟩
    have h2 : Real.sqrt x ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : x - 2 ≥ 0 := by
      nlinarith [show Real.sqrt x ≥ 0 from h2, heq]
    have h4 : x ≥ 2 := by linarith
    have h1 : Real.sqrt x ^ 2 = x := by
      rw [Real.sq_sqrt]
      linarith
    have eq1 : x = (x - 2) ^ 2 := by
      calc
        x = Real.sqrt x ^ 2 := by linarith [h1]
        _ = (x - 2) ^ 2 := by
          rw [show Real.sqrt x = x - 2 by linarith [heq]]
    have eq2 : (x - 4) * (x - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with h5 h6
    · -- x - 4 = 0
      linarith
    · -- x - 1 = 0
      nlinarith
  · -- Assume x = 4, prove x ∈ {x : ℝ | 0 ≤ x ∧ Real.sqrt x = x - 2}
    intro heq
    rw [heq]
    constructor
    · -- Show 4 ≥ 0
      norm_num
    · -- Show √4 = 4 - 2
      have h1 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      all_goals norm_num