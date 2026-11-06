import Mathlib

theorem algebra_600079 :
  {x : ℝ | x^2 - 10 * x - 29 ≠ 0 ∧ x^2 - 10 * x - 45 ≠ 0 ∧ x^2 - 10 * x - 69 ≠ 0 ∧ 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0} = {13, -3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume h, prove x = 13 or x = -3
    rintro ⟨hx1, hx2, hx3, heq⟩
    field_simp [(show (x^2 - 10 * x - 29 : ℝ) ≠ 0 by assumption), 
        (show (x^2 - 10 * x - 45 : ℝ) ≠ 0 by assumption), 
          (show (x^2 - 10 * x - 69 : ℝ) ≠ 0 by assumption) ] at heq
    have h1 : (x - 13) * (x + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h1) with
    | inl h2 =>
      left
      linarith
    | inr h3 =>
      right
      linarith
  · -- Assume x = 13 or x = -3, prove h
    rintro (h | h)
    · -- Assume x = 13
      rw [h]
      constructor
      · -- x^2 - 10 x - 29 ≠ 0
        norm_num
      constructor
      · -- x^2 - 10 x - 45 ≠ 0
        norm_num
      constructor
      · -- x^2 - 10 x - 69 ≠ 0
        norm_num
      · -- equation
        norm_num
    · -- Assume x = -3
      rw [h]
      constructor
      · -- x^2 - 10 x - 29 ≠ 0
        norm_num
      constructor
      · -- x^2 - 10 x - 45 ≠ 0
        norm_num
      constructor
      · -- x^2 - 10 x - 69 ≠ 0
        norm_num
      · -- equation
        norm_num