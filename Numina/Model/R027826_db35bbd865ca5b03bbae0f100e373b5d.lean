import Mathlib

theorem algebra_9916 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : 3 * a 7 = 5 * a 12)
    (ha' : a 0 > 0) :
    IsGreatest {∑ i in Finset.range n, a i | n} (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 + a 15 + a 16 + a 17 + a 18 + a 19) := by
  rcases ha with ⟨d, had⟩
  have h1 : a 7 = a 0 + 7 * d := by 
    rw [had 7]
    ring_nf
  have h2 : a 12 = a 0 + 12 * d := by 
    rw [had 12]
    ring_nf
  rw [h1] at h
  rw [h2] at h
  have ha0 : a 0 = -39 / 2 * d := by linarith
  have hd : d < 0 := by 
    nlinarith [ha']
  constructor
  · -- Show that $S_{20}$ is in the set.
    use 20
    norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14, had 15, had 16, had 17, had 18, had 19, ha0]
    all_goals linarith
  · -- Show that $S_{20}$ is the greatest.
    intro x hx
    rcases hx with ⟨n, hn⟩
    have h3 : ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + (d : ℝ) * (n * (n - 1) ) / 2 := by
      have h4 : ∀ n : ℕ, ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + (d : ℝ) * (n * (n - 1) ) / 2 := by
        intro n 
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [had n]
          <;> ring_nf <;> field_simp
          <;> ring
      specialize h4 n
      simpa using h4
    rw [h3] at hn
    have h4 : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 + a 15 + a 16 + a 17 + a 18 + a 19) = (20 : ℝ) * a 0 + (d : ℝ) * (20 * (20 - 1) ) / 2 := by
      simp [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14, had 15, had 16, had 17, had 18, had 19]
      all_goals ring_nf <;> field_simp
      all_goals ring
    rw [h4] 
    rw [ha0] at hn ⊢
    all_goals nlinarith [sq_nonneg ((n : ℝ) - (20 : ℝ)), sq_nonneg (d), sq_nonneg ((n : ℝ) - 20), sq_nonneg ((n : ℝ) * d), sq_nonneg ((d * (n - 20)) ), hd ]