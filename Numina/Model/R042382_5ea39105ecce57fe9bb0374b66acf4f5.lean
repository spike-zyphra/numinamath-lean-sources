import Mathlib

theorem algebra_3335 : {x : ℝ | (3 * x^2 - 3 * x - 4) / (3 * x^3 - 3 * x^2 - 3 * x - 2) = (9 * x^2 + 12 * x + 6) / (9 * x^3 + 12 * x^2 + 9 * x + 1)} = {-8 / 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side set.
    intro h
    have eq1 : (3 * x^2 - 3 * x - 4) / (3 * x^3 - 3 * x^2 - 3 * x - 2) = (9 * x^2 + 12 * x + 6) / (9 * x^3 + 12 * x^2 + 9 * x + 1) := h
    have h1 : 3 * x^3 - 3 * x^2 - 3 * x - 2 ≠ 0 := by
      by_contra h1
      have eq1' : (3 * x^2 - 3 * x - 4) / (3 * x^3 - 3 * x^2 - 3 * x - 2) = 0 := by
        rw [h1]
        norm_num
      have eq2' : (9 * x^2 + 12 * x + 6) / (9 * x^3 + 12 * x^2 + 9 * x + 1) = 0 := by
        nlinarith [eq1, eq1']
      have h2 : 9 * x^3 + 12 * x^2 + 9 * x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x * 3 + 4), sq_nonneg (x * 9 + 1), sq_nonneg (x + 8 / 3)]
      field_simp [h1, h2] at eq1 eq1' eq2'
      <;> nlinarith
    have h2 : 9 * x^3 + 12 * x^2 + 9 * x + 1 ≠ 0 := by
      by_contra h2
      have eq1' : (9 * x^2 + 12 * x + 6) / (9 * x^3 + 12 * x^2 + 9 * x + 1) = 0 := by
        rw [h2]
        norm_num
      have eq2' : (3 * x^2 - 3 * x - 4) / (3 * x^3 - 3 * x^2 - 3 * x - 2) = 0 := by
        nlinarith [eq1, eq1']
      have h1 : 3 * x^3 - 3 * x^2 - 3 * x - 2 ≠ 0 := by
        nlinarith [sq_nonneg (x * 3 + 4), sq_nonneg (x * 9 + 1), sq_nonneg (x + 8 / 3)]
      field_simp [h1, h2] at eq1 eq1' eq2'
      <;> nlinarith
    have eq2 : (3 * x^2 - 3 * x - 4) * (9 * x^3 + 12 * x^2 + 9 * x + 1) = (9 * x^2 + 12 * x + 6) * (3 * x^3 - 3 * x^2 - 3 * x - 2) := by
      field_simp [h1, h2] at eq1 ⊢
      <;> nlinarith
    have eq3 : 3 * x + 8 = 0 := by
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 8 / 3), sq_nonneg (3 * x * (x + 8 / 3)), sq_nonneg ((x * 3) + 4), sq_nonneg ((x * 9) + 1)]
    linarith
  · -- Assume x = -8/3.
    intro h
    rw [h]
    norm_num