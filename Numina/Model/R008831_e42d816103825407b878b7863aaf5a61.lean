import Mathlib

theorem algebra_10242 : {x : ℝ | 16^16 + 16^16 + 16^16 + 16^16 = (2 : ℝ)^x} = {66} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $16^{16} + \cdots = 2^x$, prove $x = 66$
    intro h
    have h1 : (16 ^ 16 + 16 ^ 16 + 16 ^ 16 + 16 ^ 16 : ℝ) = (2 : ℝ) ^ (66 : ℝ) := by 
      norm_num
    rw [h] at h1
    have h2 : x = (66 : ℝ) := by 
      apply_fun (Real.logb 2) at h1
      simp at h1 ⊢
      <;> linarith
    linarith
  · -- Assume $x = 66$, prove $16^{16} + \cdots = 2^x$
    intro h
    rw [h]
    norm_num