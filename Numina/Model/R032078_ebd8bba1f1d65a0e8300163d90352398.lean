import Mathlib

theorem algebra_279208 : {x : ℝ | 3 / 7 = x / 63} = {27} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume 3 / 7 = x / 63, prove x = 27
    intro h
    have h1 : x = 27 := by
      linarith
    exact h1
  · -- Assume x = 27, prove 3 / 7 = x / 63
    intro h
    rw [h]
    norm_num