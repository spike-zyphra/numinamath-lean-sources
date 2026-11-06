import Mathlib

theorem algebra_275080 :
  {x : ℝ | 
    let p_miss : ℝ := 1 - (1/5 + 1/4 + 1/6 + 1/8 + 1/10 + 1/12)
    10 * (1/5) + 9 * (1/4) + 8 * (1/6) + 7 * (1/8) + 6 * (1/10) + 1.7 * (1/12) - p_miss * x = 0} = {96} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the solution set
    intro h
    rcases h with h 
    norm_num at h ⊢
    linarith
  · -- Assume x = 96
    intro h 
    rw [h]
    norm_num