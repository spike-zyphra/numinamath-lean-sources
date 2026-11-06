import Mathlib

theorem algebra_302908 :
    {(x, y) : ℤ × ℤ | |x * y| + |x + y| = 1}.ncard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | |x * y| + |x + y| = 1} = {(0, 1), (0, -1), (1, 0), (-1, 0), (1, -1), (-1, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume |x * y| + |x + y| = 1, we need to show (x, y) is one of the 6 pairs
      intro h
      have h1 : |x * y| + |x + y| = 1 := h
      have h2 : |x * y| ≤ 1 := by linarith [abs_nonneg (x * y), abs_nonneg (x + y)]
      have h3 : |x + y| ≤ 1 := by linarith [abs_nonneg (x * y), abs_nonneg (x + y)]
      -- there are only two case `|x * y| = 0 ∨ |x * y| = 1`, since the absolute fucntion is nonnegative. The same for |x + y|
      have h4 : |x * y| = 0 ∨ |x * y| = 1 := by
        omega
      cases h4 with
      | inl hxy0 =>
        have hxy : x * y = 0 := abs_eq_zero.mp hxy0
        have h_sum : |x + y| = 1 := by linarith
        have h5 : x = 0 ∨ y = 0 := mul_eq_zero.mp hxy
        cases h5 with
        | inl hx =>
          rw [hx] at h_sum
          have hy1 : |y| = 1 := by simpa using h_sum
          have hy2 : y = 1 ∨ y = -1 := by
            cases eq_or_eq_neg_of_abs_eq hy1 with
            | inl h => left; linarith
            | inr h => right; linarith
          cases hy2 with
          | inl hy1 =>
            left
            exact ⟨hx, hy1⟩
          | inr hy2 =>
            right
            left
            exact ⟨hx, hy2⟩
        | inr hy =>
          rw [hy] at h_sum
          have hx1 : |x| = 1 := by simpa using h_sum
          have hx2 : x = 1 ∨ x = -1 := by
            cases eq_or_eq_neg_of_abs_eq hx1 with
            | inl h => left; linarith
            | inr h => right; linarith
          cases hx2 with
          | inl hx1 =>
            right
            right
            left
            exact ⟨hx1, hy⟩
          | inr hx2 =>
            right
            right
            right
            left
            exact ⟨hx2, hy⟩
      | inr hxy1 =>
        have h_sum : |x + y| = 0 := by linarith
        have h6 : x + y = 0 := abs_eq_zero.mp h_sum
        have h7 : |x * y| = 1 := hxy1
        have h8 : x * y = 1 ∨ x * y = -1 := by
          cases abs_cases (x * y) with
          | inl h => 
            left
            linarith
          | inr h => 
            right
            linarith
        cases h8 with
        | inl h_mul1 =>
          have h9 : x * y = 1 := h_mul1
          have h10 : y = -x := by linarith
          rw [h10] at h9
          have : x ^ 2 = -1 := by
            nlinarith
          have : x ^ 2 ≥ 0 := by
            exact sq_nonneg x
          linarith
        | inr h_mul_neg1 =>
          have h9 : x * y = -1 := h_mul_neg1
          have h10 : y = -x := by linarith
          rw [h10] at h9
          have h11 : x ^ 2 = 1 := by
            nlinarith
          have h12 : x = 1 ∨ x = -1 := by
            have h13 : x = 1 ∨ x = -1 := by
              rw [sq_eq_one_iff] at h11
              exact h11
            exact h13
          cases h12 with
          | inl hx1 =>
            have hy1 : y = -1 := by linarith
            right
            right
            right
            right
            left
            exact ⟨hx1, hy1⟩
          | inr hx_neg1 =>
            have hy1 : y = 1 := by linarith
            right
            right
            right
            right
            right
            exact ⟨hx_neg1, hy1⟩
    · -- Show that each of the 6 pairs satisfies |x * y| + |x + y| = 1
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  norm_num