import Mathlib

theorem algebra_256132 :
  { x : ℝ | x^3-5*x^2-9*x+45=0 } = { -3, 3, 5 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume x^3 - 5x^2 - 9x + 45 = 0, prove { -3, 3, 5 }
    intro h
    have h1 : x^3 - 5*x^2 - 9*x + 45 = 0 := h
    have h2 : (x - 3) * (x + 3) * (x - 5) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case x - 3 = 0, so x = 3
      have hx : x = 3 := by linarith
      rw [hx]
      norm_num
    · -- Case x + 3 = 0, so x = -3
      have hx : x = -3 := by linarith
      rw [hx]
      norm_num
    · -- Case x - 5 = 0, so x = 5
      have hx : x = 5 := by linarith
      rw [hx]
      norm_num
  · -- Assume { -3, 3, 5 }, prove x^3 - 5x^2 - 9 x + 45 = 0
    rintro (h | h | h)
    · -- Case x = -3
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num
    · -- Case x = 5
      rw [h]
      norm_num