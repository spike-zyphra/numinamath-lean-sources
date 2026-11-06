import Mathlib

theorem algebra_310216 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h : 3 * a 7 = 5 * a 12) (ha1 : a 0 > 0) :
    IsGreatest {∑ i in Finset.range n, a i | n > 0} (∑ i in Finset.range 20, a i) := by
  rcases ha with ⟨d, had⟩
  have eq1 : 3 * a 7 = 5 * a 12 := by
    simpa using h
  have eq2 : a 7 = a 0 + 7 * d := by
    rw [had 7]
    ring
  have eq3 : a 12 = a 0 + 12 * d := by
    rw [had 12]
    ring
  rw [eq2] at eq1
  rw [eq3] at eq1
  have eq4 : d = -2 * a 0 / 39 := by
    linarith
  constructor
  · -- First prove that S_20 is in the set.
    use 20
    all_goals
    norm_num
  · -- Then prove that S_20 is the greatest
    intro s hs
    rcases hs with ⟨n, hn, rfl⟩
    have h19 : (n : ℝ) ≥ 1 := by
      have hn' : n > 0 := hn
      have : n ≥ 1 := by omega
      exact_mod_cast this
    have h17 : ∑ i in Finset.range 20, a i = 20 * a 0 + 190 * d := by
      simp [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14, had 15, had 16, had 17, had 18, had 19]
      ring
    have h18 : ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + (d : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
      have h1 : ∀ n : ℕ, ∑ i in Finset.range n, a i = (n : ℝ) * a 0 + (d : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [had n]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
          <;> norm_num
          all_goals try linarith
          all_goals tauto
      specialize h1 n
      simpa using h1
    rw [h18, h17, eq4]
    by_cases h6 : (n : ℝ) ≤ 20
    · -- If n ≤ 20, then the result holds directly because the sum is increasing
      have h8 : (n : ℝ) ≤ 20 := by linarith
      nlinarith [sq_nonneg ((n : ℝ) - (20 : ℝ)), mul_pos ha1 (show (0 : ℝ) < 1 by norm_num), sq_nonneg (a 0), sq_nonneg (d), sq_nonneg (d)]
    · -- If n > 20 then works on real side
      have h7 : (n : ℝ) > 20 := by linarith
      nlinarith [sq_nonneg ((n : ℝ) - (20 : ℝ)), mul_pos ha1 (show (0 : ℝ) < 1 by norm_num), sq_nonneg (a 0), sq_nonneg (d)]