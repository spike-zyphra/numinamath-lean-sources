import Mathlib

theorem algebra_103920 : {x : ℝ | (x - 2016) * (x - 2017) * (x - 2018) = (x - 2017) * (x - 2018) * (x - 2019)} = {2017, 2018} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume (x - 2016) * (x - 2017) * (x - 2018) = (x - 2017) * (x - 2018) * (x - 2019) then x ∈ {2017, 2018}
    intro h
    have eq : (x - 2016) * (x - 2017) * (x - 2018) - (x - 2017) * (x - 2018) * (x - 2019) = 0 := by linarith
    have factored : (x - 2017) * (x - 2018) * 3 = 0 := by
      linarith [eq]
    have h1 : (x - 2017) * (x - 2018) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case x - 2017 = 0 
      left
      linarith
    · -- Case x - 2018 = 0 
      right
      linarith
  · -- Assume x ∈ {2017, 2018} then (x - 2016) * (x - 2017) * (x - 2018) = (x - 2017) * (x - 2018) * (x - 2019)
    rintro (h | h)
    · -- Case x = 2017 
      rw [show x = 2017 by linarith]
      norm_num
    · -- Case x = 2018 
      rw [show x = 2018 by linarith]
      norm_num