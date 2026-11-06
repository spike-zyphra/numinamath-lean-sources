import Mathlib

theorem algebra_303918 {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ n → n ≤ 2010 → ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n)
    (ha1 : a 1 = 2010) : a 2010 = 2 / 2011 := by

  have h1 : ∀ n, 1 ≤ n → n ≤ 2010 → ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n := ha

  have hk4 : ∀ k, 1 ≤ k → k ≤ 2010 → a k = 2 * a 1 / ((↑k * ((↑k : ℝ) + 1)) ) := by
    intro k hk1 hk10
    induction k with
    | zero =>
      linarith
    | succ k ih =>
      cases k with
      | zero =>
        norm_num at *
        all_goals
          nlinarith [ha1]
      | succ k =>
        have hk1' : 1 ≤ k + 1 := by omega
        have hk10' : k + 1 ≤ 2010 := by omega
        have hk17 : a (k + 1) = 2 * a 1 / ((↑(k + 1) * ((↑(k + 1) : ℝ) + 1)) ) := ih hk1' hk10'
        have hk8 : ∑ i in Finset.Icc 1 (k + 2), a i = (k + 2 : ℕ) ^ 2 * a (k + 2 : ℕ) := by
          apply ha
          all_goals
          omega
        have hk9 : ∑ i in Finset.Icc 1 (k + 1), a i = (k + 1 : ℕ) ^ 2 * a (k + 1 : ℕ) := by
          apply ha
          all_goals
          omega
        have eq10 : ∑ i in Finset.Icc 1 (k + 2), a i = ∑ i in Finset.Icc 1 (k + 1), a i + a (k + 2 : ℕ) := by
          rw [show Finset.Icc 1 (k + 2) = Finset.Icc 1 (k + 1) ∪ {k + 2} by
            ext x
            simp
            omega
          ]
          rw [Finset.sum_union (by
            simp
          )]
          all_goals simp
        rw [eq10] at hk8
        rw [hk9] at hk8
        simp at hk8 hk17 ⊢
        field_simp at hk8 hk17 ⊢
        ring_nf at hk8 hk17 ⊢
        nlinarith [sq_nonneg (a (k + 2 : ℕ) : ℝ), sq_nonneg (a (k + 1 : ℕ) : ℝ), sq_nonneg ((↑k : ℝ) ) ]

  have hk5 : a 2010 = 2 * a 1 / ((↑(2010 : ℕ) * ((↑(2010 : ℕ) : ℝ) + 1)) ) := by
    specialize hk4 2010 (by norm_num) (by norm_num)
    simpa using hk4

  rw [hk5]
  rw [ha1]
  norm_num