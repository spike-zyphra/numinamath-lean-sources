import Mathlib

theorem algebra_293135 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (ha1 : a 0 > 0) (h : 3 * a 7 = 5 * a 12) :
    IsGreatest {x | ∃ n, x = ∑ i in Finset.range n, a i} (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 + a 15 + a 16 + a 17 + a 18 + a 19) := by
  rcases ha with ⟨d, had⟩
  have eq1 : a 7 = a 0 + 7 * d := by
    specialize had 7
    norm_num at had ⊢
    linarith
  have eq2 : a 12 = a 0 + 12 * d := by
    specialize had 12
    norm_num at had ⊢
    linarith
  rw [eq1] at h
  rw [eq2] at h
  have h1 : a 0 = -39 / 2 * d := by
    nlinarith
  have h2 : d < 0 := by
    nlinarith
  constructor
  · -- Show that the given sum is in the set
    use 20
    all_goals
      simp [Finset.sum_range_succ]
  · -- Show that the given sum is the greatest
    intro x hx
    rcases hx with ⟨n, hn⟩
    have eq4 : ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
      have eq3 : ∀ (i : ℕ), a i = a 0 + d * (i : ℝ) := by
        intro i
        specialize had i
        simpa using had
      have h4 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          have eq5 : ∑ i in Finset.range (n + 1), a i = ∑ i in Finset.range n, a i + a n := by
            rw [Finset.sum_range_succ]
          rw [eq5, ih]
          have eq6 : a n = a 0 + d * (n : ℝ) := by
            specialize eq3 n
            simpa using eq3
          rw [eq6]
          field_simp at *
          ring_nf
      exact h4 n
    have eq5 : x = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
      rw [hn]
      rw [eq4]
    have eq6 : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 + a 15 + a 16 + a 17 + a 18 + a 19 : ℝ) = (20 : ℝ) / 2 * (2 * a 0 + (19 : ℝ) * d) := by
      have eq3 : ∀ (i : ℕ), a i = a 0 + d * (i : ℝ) := by
        intro i
        specialize had i
        simpa using had
      simp [Finset.sum_range_succ, eq3 1, eq3 2, eq3 3, eq3 4, eq3 5, eq3 6, eq3 7, eq3 8, eq3 9, eq3 10, eq3 11, eq3 12, eq3 13, eq3 14, eq3 15, eq3 16, eq3 17, eq3 18, eq3 19]
      ring
    have h4 : (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) ≤ (20 : ℝ) / 2 * (2 * a 0 + (19 : ℝ) * d) := by
      rw [show a 0 = -39 / 2 * d by linarith [h1]]
      nlinarith [sq_nonneg ((n : ℝ) - 20), sq_nonneg ((n : ℝ) - 20), sq_nonneg (d), sq_nonneg ((n : ℝ) - 20), sq_nonneg ((n : ℝ) - 20)]
    nlinarith [eq5, eq6, h4]