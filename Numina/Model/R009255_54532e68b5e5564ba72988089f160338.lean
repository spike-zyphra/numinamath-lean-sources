import Mathlib

theorem algebra_619216 : {x : ℝ | x ^ 2 = 144} = {12, -12} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- First direction: if x^2 = 144 then x in {-12, 12}
    intro h
    have h1 : x^2 - 144 = 0 := by linarith
    have h2 : (x - 12) * (x + 12) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case x - 12 = 0, so x = 12
      left
      linarith
    · -- Case x + 12 = 0, so x = -12
      right
      linarith
  · -- Second direction: if x in {-12, 12} then x^2 = 144
    rintro (h | h)
    · -- Case x = 12
      rw [h]
      norm_num
    · -- Case x = -12
      rw [h]
      norm_num