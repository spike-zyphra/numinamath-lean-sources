import Mathlib

theorem algebra_169032 (a : ℕ → ℝ) (ha1 : a 1 = 7) (han : ∀ n ≥ 1, a (n + 1) / a n = a n + 2) :
    IsLeast {n | 0 < n ∧ a n > 4 ^ 2018} 12 := by

  have h1 : ∀ n ≥ 1, a (n + 1) = a n * (a n + 2) := by
    intro n hn
    have h2 : a (n + 1) / a n = a n + 2 := han n hn
    have h3 : a n > 0 := by
      have h4 : ∀ k ≥ 1, a k > 0 := by
        intro k hk
        induction k with
        | zero => 
          linarith
        | succ k ih =>
          by_cases h : k = 0
          · rw [h]
            rw [ha1]
            all_goals norm_num
          · 
            have hk' : k ≥ 1 := by
              omega
            have h5 : a (k + 1) > 0 := by
              have h6 : a (k + 1) / a k = a k + 2 := han k (by omega)
              have h7 : a k > 0 := ih (by omega)
              have h9 : a k ≠ 0 := by linarith [h7]
              have h10 : a (k + 1) = a k * (a k + 2) := by
                have h11 : a (k + 1) / a k = a k + 2 := h6
                field_simp at h11 ⊢
                nlinarith
              nlinarith [sq_nonneg (a k)]
            exact h5
      specialize h4 n hn
      linarith
    have h9 : a n ≠ 0 := by linarith [h3]
    have h10 : a (n + 1) = a n * (a n + 2) := by
      have h11 : a (n + 1) / a n = a n + 2 := h2
      have h9 : a n ≠ 0 := by
        linarith [h3]
      field_simp at h11 ⊢
      nlinarith
    linarith

  constructor
  · -- Show 12 is in the set
    constructor
    · norm_num
    · -- Show a 12 > 4 ^ 2018
      norm_num [ha1, h1]

  · -- Show that 12 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_gt⟩
    by_contra h
    push_neg at h
    have h2 : n < 12 := by linarith
    have h143 : a n ≤ (4 : ℝ) ^ 2018 := by
      have h120 : n < 12 := by linarith
      have h117 : n ≥ 1 := by linarith
      interval_cases n <;> norm_num [ha1, h1] at *
    nlinarith