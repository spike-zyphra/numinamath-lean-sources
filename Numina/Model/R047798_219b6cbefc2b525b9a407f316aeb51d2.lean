import Mathlib

set_option maxRecDepth 5000


theorem algebra_14852 : IsLeast {m : ℤ | 0 < m ∧ (∃ r s : ℤ, ∀ x : ℝ, x ^ 2 +
    m * x + 2008 = (x + r) * (x + s))} 259 := by
  constructor
  · -- Show 259 is in the set
    constructor
    · norm_num
    · use 8, 251
      intro x
      norm_num
      <;> nlinarith
  · -- Now need to show it's the least
    intro m hm
    rcases hm with ⟨hm_pos, r, s, h_eq⟩
    have h1 := h_eq 0
    simp at h1
    have h2 := h_eq 1
    simp at h2
    have h3 : r * s = 2008 := by
      have h4 : (r : ℝ) * (s : ℝ) = 2008 := by
        nlinarith
      norm_cast at h4 ⊢
    have eq3 : m = r + s := by
      have eq4 : (m : ℝ) = (r : ℝ) + (s : ℝ) := by
        nlinarith
      norm_cast at eq4 ⊢
    by_contra h
    push_neg at h
    have h4 : m < 259 := by omega
    have h5 : r * s = 2008 := h3
    have h6 : r > 0 := by
      by_contra h7
      push_neg at h7
      have h8 : r ≤ 0 := by omega
      have h9 : s ≤ 0 := by
        nlinarith [sq_nonneg (r : ℤ), sq_nonneg (s : ℤ), h5]
      have h10 : m ≤ 0 := by
        nlinarith [sq_nonneg (r : ℤ), sq_nonneg (s : ℤ), h5, eq3]
      linarith
    have h7 : s > 0 := by
      by_contra h8
      push_neg at h8
      have h9 : s ≤ 0 := by omega
      nlinarith [sq_nonneg (r : ℤ), sq_nonneg (s : ℤ), h5, h6]
    have h8 : r ≤ 258 := by nlinarith
    have h9 : s ≤ 258 := by nlinarith
    interval_cases r <;> omega