import Mathlib

theorem algebra_10402: {x : ℝ | (2008 + x)^2 = x^2 } = {-1004} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (2008 + x)^2 = x^2, we need to prove x = -1004
    intro h
    have h1 : (2008 + x) ^ 2 - x ^ 2 = 0 := by linarith
    have h2 : (2008 : ℝ) * (2008 + 2 * x) = 0 := by 
      ring_nf at h1 ⊢
      linarith 
    cases' (mul_eq_zero.mp h2) with h3 h4 
    · -- h3 : 2008 = 0, which is false 
      exfalso 
      norm_num at h3 
    · -- h4 : 2008 + 2 * x = 0 
      linarith 
  · -- Assume x = -1004, we need to prove (2008 + x)^2 = x^2
    intro h 
    rw [h]
    norm_num