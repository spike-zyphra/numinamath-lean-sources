import Mathlib

theorem algebra_1788 : {a : ℝ | Polynomial.coeff ((Polynomial.C 2 + Polynomial.C a * Polynomial.X) ^ 6) 2 = 60} = {-1/2, 1/2} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  have h1 : Polynomial.coeff ((Polynomial.C 2 + Polynomial.C a * Polynomial.X) ^ 6) 2 = 240 * a^2 := by
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, pow_two, pow_succ, Polynomial.coeff_C, Polynomial.coeff_X, mul_assoc]
    all_goals ring
  rw [h1]
  constructor
  · -- Assume 240 * a^2 = 60, prove a = -1/2 or a = 1/2
    intro h
    have h2 : a^2 = 1 / 4 := by
      nlinarith
    have h3 : a = 1 / 2 ∨ a = -1 / 2 := by
      have h4 : a^2 - 1 / 4 = 0 := by linarith
      have h5 : (a - 1 / 2) * (a + 1 / 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h5) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        linarith
    tauto
  · -- Assume a = -1/2 or a = 1/2, prove 240 * a^2 = 60
    rintro (h | h)
    · -- Case a = -1/2
      rw [h]
      norm_num
    · -- Case a = 1/2
      rw [h]
      norm_num