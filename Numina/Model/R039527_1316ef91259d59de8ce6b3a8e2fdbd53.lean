import Mathlib

  theorem algebra_22025 : {x : ℝ | (x - 3)^3 + (x - 7)^3 = (2 * x - 10)^3} = {3, 5, 7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, prove the forward implication: if (x - 3)^3 + (x - 7)^3 = (2 * x - 10)^3, then x ∈ {3, 5, 7}
    intro h
    have h1 : (x - 3) ^ 3 + (x - 7) ^ 3 - (2 * x - 10) ^ 3 = 0 := by linarith
    have h2 : (x - 3) * (x - 5) * (x - 7) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- x - 3 = 0, so x = 3
      have hx : x = 3 := by linarith
      left
      exact hx
    · -- x - 5 = 0, so x = 5
      have hx : x = 5 := by linarith
      right
      left
      exact hx
    · -- x - 7 = 0, so x = 7
      have hx : x = 7 := by linarith
      right
      right
      exact hx
  · -- Now prove the reverse: if x ∈ {3, 5, 7}, then (x - 3)^3 + (x - 7)^3 = (2 * x - 10)^3
    rintro (rfl | rfl | rfl)
    · -- Check x = 3
      norm_num
    · -- Check x = 5
      norm_num
    · -- Check x = 7
      norm_num