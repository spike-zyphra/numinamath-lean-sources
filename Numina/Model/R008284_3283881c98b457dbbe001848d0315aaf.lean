import Mathlib

theorem algebra_252736 : {x : ℝ | (10 : ℝ) ^ (x ^ 2 + x - 2) = 1} = {-2, 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume (10 : ℝ) ^ (x ^ 2 + x - 2) = 1, prove x ∈ {-2, 1}
    intro h
    have h1 : x^2 + x - 2 = (0 : ℝ) := by
      have h2 : x^2 + x - 2 = (0 : ℝ) := by
        apply_fun (Real.logb 10) at h
        simp at h ⊢
        <;> linarith
      linarith 
    have h3 : (x - 1) * (x + 2) = 0 := by
      ring_nf at h1 ⊢ 
      linarith 
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case x - 1 = 0, so x = 1 
      right 
      linarith 
    · -- Case x + 2 = 0, so x = -2
      left 
      linarith 
  · -- Assume x ∈ {-2, 1}, prove (10 : ℝ) ^ (x ^ 2 + x - 2) = 1
    rintro (h | h)
    · -- Case x = -2 
      rw [h]
      norm_num 
    · -- Case x = 1 
      rw [h]
      norm_num