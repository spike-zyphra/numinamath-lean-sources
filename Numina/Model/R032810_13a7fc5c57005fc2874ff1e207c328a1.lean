import Mathlib

theorem algebra_9166 : {x : ℤ | x > 0 ∧ x < √2} = {1} := by
  have h1 : (1 : ℝ) < √2 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : √2 < (2 : ℝ) := by
    rw [Real.sqrt_lt] <;> norm_num

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, prove it is 1.
    intro h
    rcases h with ⟨hx1, hx2⟩
    have h3 : x = 1 := by
      by_contra h
      push_neg at h
      have h4 : x ≥ (1 : ℤ) := by linarith
      have h5 : x ≥ (2 : ℤ) := by
        omega
      have h6 : (x : ℝ) ≥ (2 : ℝ) := by
        exact_mod_cast h5
      have h6 : (x : ℝ) < (Real.sqrt (2 : ℝ) ) := by
        simpa using hx2
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    exact_mod_cast h3
  · -- Assume it is 1, prove in the left side.
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Show that 1 < √2
      have h1 : (1 : ℝ) < √2 := by
        rw [Real.lt_sqrt] <;> norm_num
      exact_mod_cast h1