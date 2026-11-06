import Mathlib

theorem algebra_215798 {a : ℕ → ℝ} (h : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha : a 0 = 3) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by

  have eq1 : ∀ n, a n ≠ 0 := by
    intro n
    have h1 : ∀ n, a n > 0 := by
      intro n
      induction n with
      | zero =>
        rw [ha]
        norm_num
      | succ n ih =>
        have eq2 := h n
        nlinarith [sq_pos_of_pos ih, sq_nonneg (a n - 3), sq_nonneg (a (n + 1) - 3)]
    specialize h1 n
    linarith

  have eq2 : ∀ (n : ℕ), 1 / a n = (2 ^ (n + 1) - 1) / 3 := by
    intro n
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      have eq3 := h n
      have eq4 : a (n + 1) = (3 * a n) / (6 + a n) := by
        have eq3 := h n
        have hne1 : a n ≠ 0 := eq1 n
        have hne2 : (6 + a n) ≠ 0 := by
          have h21 : a n > 0 := by
            have h1 : ∀ (n : ℕ), a n > 0 := by
              intro n
              induction n with
              | zero =>
                rw [ha]
                norm_num
              | succ n ih =>
                have eq2 := h n
                nlinarith [sq_pos_of_pos ih, sq_nonneg (a n - 3), sq_nonneg (a (n + 1) - 3)]
            specialize h1 n
            linarith
          nlinarith
        field_simp [hne2] at eq3 ⊢
        nlinarith [eq3]
      have eq5 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := by
        rw [eq4]
        have hne1 : a n ≠ 0 := eq1 n
        field_simp [hne1]
        <;> ring
      rw [eq5, ih]
      field_simp at *
      ring_nf

  have h3 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by
    intro n
    induction n with
    | zero =>
      norm_num [ha, eq2]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [eq2]
      ring_nf

  specialize h3 n
  simpa using h3