import Mathlib

theorem algebra_108019 (a S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i)
    (ha : ∃ d, ∀ n, a (n + 1) = a n + d) (hS1 : S 2010 - S 1 = 1) :
    S 2011 = 2011 / 2009 := by
  rcases ha with ⟨d, had⟩
  have h1 : ∀ n, S n = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
    intro n
    rw [hS n]
    have h2 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have h3 : a n = a 0 + (n : ℝ) * d := by
          have h4 : ∀ (k : ℕ), a (k + 1) = a k + d := by
            intro k
            specialize had k
            simpa using had
          have h5 : ∀ (k : ℕ), a k = a 0 + (k : ℝ) * d := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              have h7 : a (k + 1) = a k + d := h4 k
              rw [h7, ih]
              simp at *
              all_goals ring
          specialize h5 n
          simpa using h5
        rw [h3]
        field_simp at *
        ring_nf
    specialize h2 n
    simpa using h2
  have h2010 : S 2010 = (2010 : ℝ) / 2 * (2 * a 0 + (2010 - 1 : ℝ) * d) := by
    specialize h1 2010
    norm_num at h1 ⊢
    linarith
  have h1_1 : S 1 = (1 : ℝ) / 2 * (2 * a 0 + (1 - 1 : ℝ) * d) := by
    specialize h1 1
    norm_num at h1 ⊢
    linarith
  rw [h2010, h1_1] at hS1
  have h_eq : 2009 * (a 0 + 1005 * d) = 1 := by
    norm_num at hS1 ⊢
    linarith
  have h2011 : S 2011 = (2011 : ℝ) / 2 * (2 * a 0 + (2011 - 1 : ℝ) * d) := by
    specialize h1 2011
    norm_num at h1 ⊢
    linarith
  have h_eq2 : S 2011 = 2011 * (a 0 + 1005 * d) := by
    rw [h2011]
    ring_nf
  have h_eq3 : a 0 + 1005 * d = 1 / 2009 := by
    linarith
  rw [h_eq2]
  rw [h_eq3]
  all_goals norm_num