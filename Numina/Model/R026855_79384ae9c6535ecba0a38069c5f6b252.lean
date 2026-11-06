import Mathlib

theorem algebra_116207 {a : ℕ → ℝ} (ha : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha0 : a 0 = 3) :
    ∑ i in Finset.range (n + 1), (1 / a i) = (2 ^ (n + 2) - n - 3) / 3 := by
  have h1 : ∀ n, a n ≠ 0 := by
    intro n
    have h2 : ∀ n : ℕ, a n ≠ 0 := by
      intro n
      induction n with
      | zero =>
        rw [ha0]
        norm_num
      | succ n ih =>
        by_contra h
        have h3 : (3 - a (n + 1)) * (6 + a n) = 18 := ha (n)
        rw [show a (n + 1) = (0 : ℝ) by linarith] at h3
        have h4 : a n = 0 := by
          nlinarith
        contradiction
    exact h2 n
  -- Derive the recurrence for the reciprocals
  have h2 : ∀ n, 1 / a n = (2 ^ (n + 1) - 1) / 3 := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      norm_num
    | succ n ih =>
      have h3 : (3 - a (n + 1)) * (6 + a n) = 18 := ha n
      have h4 : a (n + 1) = 3 * a n / (6 + a n) := by
        have h5 : 6 + a n ≠ 0 := by
          by_contra h
          have h6 : a n = -6 := by linarith
          rw [h6] at h3
          nlinarith
        field_simp [h5, h1 n, h1 (n + 1)]
        nlinarith [sq_pos_of_ne_zero (h1 n), sq_nonneg (a (n + 1) - 3), sq_nonneg (a n + 6)]
      have h5 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := by
        rw [h4]
        have h6 : a n ≠ 0 := h1 n
        field_simp [h6]
        <;> ring_nf 
      rw [h5, ih]
      field_simp at *
      ring_nf
  -- Derive the sum of the reciprocals
  have h3 : ∀ n, ∑ i in Finset.range (n + 1), (1 / a i) = (2 ^ (n + 2) - n - 3) / 3 := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_range_succ, h2 0, ha0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h2 (n + 1)]
      <;> field_simp at *
      <;> ring_nf
  -- Final result
  specialize h3 n
  simpa using h3