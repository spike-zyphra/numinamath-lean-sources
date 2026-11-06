import Mathlib

theorem algebra_63 : {x : ℕ | 2^20 - 2^19 = 2^x} = {19} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume 2^20 - 2^19 = 2^x, prove x = 19
    intro h
    have eq1 : 2 ^ 20 - 2 ^ 19 = 2 ^ 19 := by
      norm_num
    have h2 : 2 ^ 19 = 2 ^ x := by 
      omega
    have h3 : 19 = x := by 
      exact Nat.pow_right_injective (by norm_num) h2
    linarith
  · -- Assume x = 19, prove 2^20 - 2^19 = 2^x
    intro h
    rw [h]
    all_goals norm_num