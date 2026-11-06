import Mathlib

theorem algebra_90511 : {x : ℝ | (x + 1)^5 + (x + 1)^4 * (x - 1) + (x + 1)^3 * (x - 1)^2 +
    (x + 1)^2 * (x - 1)^3 + (x + 1) * (x - 1)^4 + (x - 1)^5 = 0} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume that the polynomial equals zero, prove x = 0.
    intro h
    have eq1 : (x + 1)^5 + (x + 1)^4 * (x - 1) + (x + 1)^3 * (x - 1)^2 + (x + 1)^2 * (x - 1)^3 + (x + 1) * (x - 1)^4 + (x - 1)^5 = 0 := h
    ring_nf at eq1
    have h2 : x ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 0)]
    have h3 : x = 0 := by
      rw [sq_eq_zero_iff] at h2
      linarith
    exact h3
  · -- Assume x = 0, prove the polynomial equals zero.
    intro h
    rw [h]
    norm_num