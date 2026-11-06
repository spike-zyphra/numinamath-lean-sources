import Mathlib

theorem algebra_6581 :
  ∑ᶠ x ∈ {x : ℝ | |x^2 + 3 * x - 1| = 3}, x = -6 := by
  have h1 : {x : ℝ | |x^2 + 3 * x - 1| = 3} = {-2, -1, 1, -4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume that |x^2 + 3x - 1| = 3, prove that x ∈ {-2, -1, 1, -4}
      intro h
      cases eq_or_eq_neg_of_abs_eq h with
      | inl h1 =>
        have h2 : x^2 + 3 * x - 4 = 0 := by linarith
        have : (x - 1) * (x + 4) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h3 h4
        · -- x - 1 = 0
          right
          right
          left
          linarith
        · -- x + 4 = 0
          right
          right
          right
          linarith
      | inr h2 =>
        have h4 : x^2 + 3 * x + 2 = 0 := by linarith
        have : (x + 1) * (x + 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h5 h6
        · -- x + 1 = 0
          right
          left
          linarith
        · -- x + 2 = 0
          left
          linarith
    · -- Assume that x ∈ {-2, -1, 1, -4}, prove that |x^2 + 3 x - 1| = 3
      rintro (h | h | h | h)
      · -- x = -2
        rw [h]
        norm_num [abs_eq]
      · -- x = -1
        rw [h]
        norm_num [abs_eq]
      · -- x = 1
        rw [h]
        norm_num [abs_eq]
      · -- x = -4
        rw [h]
        norm_num [abs_eq]
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> try norm_num
  <;> try linarith
  all_goals
    norm_num
    <;> linarith