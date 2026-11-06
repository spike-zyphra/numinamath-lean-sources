import Mathlib

theorem algebra_214321 :
    ∑ᶠ x ∈ {x : ℝ | abs (x ^ 2 - 12 * x + 34) = 2}, x = 18 := by

  have h1 : {x : ℝ | abs (x ^ 2 - 12 * x + 34) = 2} = {4, 6, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume abs (x^2 -12 x +34) = 2, prove x ∈ {4, 6, 8}
      intro h
      cases abs_choice (x ^ 2 - 12 * x + 34) with
      | inl h_eq =>
        have h_eq' : x ^ 2 - 12 * x + 34 = 2 := by linarith
        have h_eq2 : x ^ 2 - 12 * x + 32 = 0 := by linarith
        have h_factor : (x - 8) * (x - 4) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h_factor) with
        | inl h8 =>
          right
          right
          linarith
        | inr h4 =>
          left
          linarith
      | inr h_eq =>
        have h_eq' : x ^ 2 - 12 * x + 34 = -2 := by linarith
        have h_eq2 : x ^ 2 - 12 * x + 36 = 0 := by linarith
        have h_factor : (x - 6) ^ 2 = 0 := by
          nlinarith
        have h6 : x - 6 = 0 := by
          apply pow_eq_zero 
          exact h_factor
        have hx : x = 6 := by linarith
        right
        left
        linarith
    · -- Assume x ∈ {4, 6, 8}, prove abs (x^2 -12 x +34) = 2
      rintro (rfl | rfl | rfl)
      · -- x = 4
        norm_num [abs_of_nonneg]
      · -- x = 6
        norm_num [abs_of_nonpos]
      · -- x = 8
        norm_num [abs_of_nonneg]

  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> try { norm_num }
  <;> try { tauto }