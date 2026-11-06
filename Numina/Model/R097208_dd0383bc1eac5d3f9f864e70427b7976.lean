import Mathlib

theorem algebra_198085 (b : ℕ) (hb : b = Set.ncard {x : ℝ | abs (x - abs (2 * x + 1)) = 3}) :
    b = 2 := by
  have h2 : {x : ℝ | abs (x - abs (2 * x + 1)) = 3} = {2, -4 / 3} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (x - abs (2 * x + 1)) = 3, prove x ∈ {2, -4 / 3}
      intro h
      have h_eq : abs (x - abs (2 * x + 1)) = 3 := h
      by_cases h1 : 2 * x + 1 ≥ 0
      · -- Case where 2x + 1 ≥ 0
        have h_abs1 : abs (2 * x + 1) = 2 * x + 1 := by
          rw [abs_of_nonneg h1]
        rw [h_abs1] at h_eq
        have h_eq1 : abs (x - (2 * x + 1)) = 3 := h_eq
        have h_eq2 : abs (-x - 1) = 3 := by
          have h : x - (2 * x + 1) = -x - 1 := by ring
          rw [h] at h_eq1
          linarith
        cases eq_or_eq_neg_of_abs_eq h_eq2 with
        | inl h2 =>
          linarith
        | inr h2 =>
          have h3 : x = 2 := by linarith
          left
          exact h3
      · -- Case where 2x + 1 < 0
        have h_abs2 : abs (2 * x + 1) = -(2 * x + 1) := by
          rw [abs_of_neg (lt_of_not_ge h1)]
        rw [h_abs2] at h_eq
        have h_eq1 : abs (x - -(2 * x + 1)) = 3 := h_eq
        have h_eq2 : abs (3 * x + 1) = 3 := by
          have h : x - -(2 * x + 1) = 3 * x + 1 := by ring
          rw [h] at h_eq1
          linarith
        cases eq_or_eq_neg_of_abs_eq h_eq2 with
        | inl h2 =>
          linarith
        | inr h2 =>
          have h3 : x = -4 / 3 := by linarith
          right
          linarith
    · -- Assume x ∈ {2, -4 / 3}, prove abs (x - abs (2 * x + 1)) = 3
      rintro (h | h)
      · -- Case x = 2
        rw [h]
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- Case x = -4 / 3
        rw [h]
        norm_num [abs_of_nonneg, abs_of_neg]
  rw [h2] at hb
  rw [hb]
  have h3 : (2 : ℝ) ≠ -4 / 3 := by norm_num
  rw [Set.ncard_pair h3]
  all_goals norm_num