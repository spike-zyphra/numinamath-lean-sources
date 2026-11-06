import Mathlib

theorem algebra_186438 {a S : ℕ → ℝ} {n : ℕ} (hS : ∀ k, S k = ∑ i in Finset.range k, a i)
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hS6 : S 6 = 36) (hS12 : S 12 = 144)
    (hS6n : S (6 * n) = 576) : n = 4 := by
  rcases ha with ⟨d, hd⟩
  have h6 : S 6 = 6 * a 0 + 15 * d := by
    rw [hS 6]
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4, hd 5]
    ring
  have h12 : S 12 = 12 * a 0 + 66 * d := by
    rw [hS 12]
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4, hd 5, hd 6, hd 7, hd 8, hd 9, hd 10, hd 11]
    ring
  rw [h6] at hS6
  rw [h12] at hS12
  have h1 : 2 * a 0 + 5 * d = 12 := by
    linarith
  have h2 : 2 * a 0 + 11 * d = 24 := by
    linarith
  have h3 : d = 2 := by
    linarith [h1, h2]
  have h4 : a 0 = 1 := by
    linarith [h1, h3]
  have h6n : S (6 * n) = 6 * (n : ℝ) * a 0 + ( (6 * (n : ℝ) - 1) * (6 * (n : ℝ)) / 2 ) * d := by
    rw [hS (6 * n)]
    have h : ∀ (n : ℕ), ∑ i in Finset.range (6 * n), a i = 6 * (n : ℝ) * a 0 + ( (6 * (n : ℝ) - 1) * (6 * (n : ℝ)) / 2 ) * d := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [show 6 * (n + 1 : ℕ) = 6 * (n : ℕ) + 6 by ring]
        rw [Finset.sum_range_add]
        rw [ih]
        simp [Finset.sum_range_succ, hd (6 * (n : ℕ)), hd (6 * (n : ℕ) + 1), hd (6 * (n : ℕ) + 2), hd (6 * (n : ℕ) + 3), hd (6 * (n : ℕ) + 4), hd (6 * (n : ℕ) + 5)]
        ring_nf
    specialize h n
    simpa using h
  rw [h6n] at hS6n
  rw [h4, h3] at hS6n
  have h5 : (n : ℝ) ^ 2 = 16 := by
    ring_nf at hS6n
    nlinarith
  have h6 : n ^ 2 = 16 := by
    exact_mod_cast h5
  have h7 : n ≤ 4 := by
    nlinarith
  interval_cases n <;> try { omega }
  all_goals
    try { tauto }
    all_goals
      try { nlinarith }