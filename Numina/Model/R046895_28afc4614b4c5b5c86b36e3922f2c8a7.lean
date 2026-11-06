import Mathlib

theorem algebra_284499 :
  {x : ℝ | x > 0 ∧ 3 * x + (15/100) * x = 6300} = {2000} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x > 0 ∧ 3 * x + (15/100) * x = 6300, need to prove x = 2000
    rintro ⟨hx1, hx2⟩
    have h1 : 3 * x + (15 / 100) * x = 6300 := by
      linarith
    have h2 : x = 2000 := by
      linarith
    linarith
  · -- Assume x = 2000, need to prove x > 0 ∧ 3 * x + (15/100) * x = 6300
    intro hx1
    rw [hx1]
    constructor
    · norm_num
    · norm_num