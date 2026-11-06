import Mathlib

theorem algebra_208516 :
  { p : ℝ | ∃ x y, x^3-7*x+p=0 ∧ y^3-7*y+p=0 ∧ |x-y| = 1 }
  = {6, -6} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
          Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume p in the left side, prove p in the right side
    rintro ⟨x, y, h1, h2, h3⟩
    have h4 : (x - y) * (x^2 + x * y + y^2 - 7) = 0 := by
      have eq1 : x^3 - 7 * x + p = 0 := by linarith
      have eq2 : y^3 - 7 * y + p = 0 := by linarith
      have eq3 : x^3 - 7 * x + p - (y^3 - 7 * y + p) = 0 := by
        linarith
      have eq4 : x^3 - y^3 - 7 * (x - y) = 0 := by
        nlinarith 
      nlinarith [sq_nonneg (x^2 + x * y + y^2)]
    have h5 : x - y ≠ 0 := by
      by_contra h
      have : |x - y| = 0 := by
        rw [h]
        norm_num
      linarith
    have h6 : x^2 + x * y + y^2 - 7 = 0 := by
      apply (mul_right_inj' h5).mp
      linarith
    have h7 : x - y = 1 ∨ x - y = -1 := by
      cases eq_or_eq_neg_of_abs_eq h3 with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    cases h7 with
    | inl h8 =>
      have hy : y = x - 1 := by
        linarith
      rw [hy] at h6
      have h8 : (x - 2) * (x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- Case x = 2
        have hx : x = 2 := by linarith
        have hp : p = 6 := by
          rw [hx] at h1
          nlinarith
        left
        linarith
      · -- Case x = -1
        have hx : x = -1 := by linarith
        have hp : p = -6 := by
          rw [hx] at h1
          nlinarith
        right
        linarith
    | inr h9 =>
      have hy : y = x + 1 := by
        linarith
      rw [hy] at h6
      have h8 : (x + 2) * (x - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- Case x = -2
        have hx : x = -2 := by linarith
        have hp : p = -6 := by
          rw [hx] at h1
          nlinarith
        right
        linarith
      · -- Case x = 1
        have hx : x = 1 := by linarith
        have hp : p = 6 := by
          rw [hx] at h1
          nlinarith
        left
        linarith
  · -- Assume p in the right side, prove p in the left side
    rintro (rfl | rfl)
    · -- Case p = 6
      use 2, 1
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num [abs_of_pos]
    · -- Case p = -6
      use -1, -2
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num [abs_of_pos]