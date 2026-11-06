import Mathlib

theorem algebra_282874 : 
  {x : ℝ | (x - 5)^4 + (x - 4)^4 = 97} = {2, 7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume h: (x-5)^4 + (x-4)^4 = 97, prove x = 2 ∨ x = 7
    intro h
    have h_eq : (x - 5) ^ 4 + (x - 4) ^ 4 = 97 := h
    have h1 : (x - 2) * (x - 7) * (x^2 - 9 * x + 28) = 0 := by
      ring_nf at h_eq ⊢
      nlinarith [sq_nonneg (x ^ 2 - 9 * x + 28), sq_nonneg (x - 2), sq_nonneg (x - 7)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- case where $x - 2 = 0$, so $x = 2$
      left
      linarith
    · -- case where $x - 7 = 0$, so $x = 7$
      right
      linarith
    · -- case where $x^2 - 9x + 28 = 0$
      have h_eq2 : x^2 - 9 * x + 28 = 0 := by
        linarith
      nlinarith [sq_nonneg (x - 9 / 2)]
  · -- Assume x = 2 or x = 7, prove (x - 5) ^ 4 + (x - 4) ^ 4 = 97
    rintro (h | h)
    · -- If x = 2
      rw [h]
      norm_num
    · -- If x = 7
      rw [h]
      norm_num