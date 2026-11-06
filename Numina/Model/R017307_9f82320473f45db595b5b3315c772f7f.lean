import Mathlib

theorem algebra_123373 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : 3 * a 8 = 5 * a 13)
    (ha' : a 1 > 0) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i) :
    IsGreatest {x | ∃ n, x = S n ∧ n ≤ 20} (S 20) := by
  rcases ha with ⟨d, had⟩
  have h6 : a 1 = a 0 + d := by
    specialize had 1
    norm_num at had ⊢
    linarith
  have h8 : a 8 = a 0 + 8 * d := by
    specialize had 8
    norm_num at had ⊢
    linarith
  have h13 : a 13 = a 0 + 13 * d := by
    specialize had 13
    norm_num at had ⊢
    linarith
  rw [h8, h13] at h
  have eq1 : a 0 = -41 / 2 * d := by
    linarith
  have h6' : a 1 = -39 / 2 * d := by
    rw [h6, eq1]
    linarith
  have h7 : d < 0 := by
    nlinarith [ha']
  have eq2 : ∀ (n : ℕ), S n = (d / 2) * (n : ℝ) * ((n : ℝ) - 42) := by
    intro n
    rw [hS n]
    have h8 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (d / 2) * (n : ℝ) * ((n : ℝ) - 42) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [eq1, had, add_mul, mul_add, mul_comm] at *
        field_simp at *
        ring_nf
        <;> nlinarith [sq_nonneg (d), sq_nonneg ((n: ℝ))]
    specialize h8 n
    linarith
  constructor
  · -- Show $S_20$ is in the set
    use 20
    all_goals norm_num [eq2]
  · -- Show $S_20$ is the greatest
    intro x hx
    rcases hx with ⟨n, hn, hn2⟩
    rw [hn]
    have h8 : n ≤ 20 := by linarith
    have eq3 : S n = (d / 2) * (n : ℝ) * ((n : ℝ) - 42) := by
      apply eq2
    have eq4 : S 20 = (d / 2) * (20 : ℝ) * ((20 : ℝ) - 42) := by
      apply eq2
    have h9 : (n : ℝ) ≤ (20 : ℝ) := by
      exact_mod_cast h8
    have h13 : (d / 2 : ℝ) < 0 := by
      nlinarith
    have h10 : (n : ℝ) * ((n : ℝ) - 42) ≥ (20 : ℝ) * ((20 : ℝ) - 42) := by
      nlinarith [sq_nonneg ((n : ℝ) - 20), sq_nonneg ((n : ℝ) - 22), sq_nonneg ((20 : ℝ) - 22), sq_nonneg ((n : ℝ) - (20 : ℝ)), h8]
    have h11 : S n ≤ S 20 := by
      rw [eq3, eq4]
      nlinarith [h13, h10]
    linarith