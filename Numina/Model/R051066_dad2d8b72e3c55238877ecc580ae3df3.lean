import Mathlib

theorem algebra_305032 {a S : ℕ → ℝ} (hS : ∀ n, S n = ∑ i in Finset.range n, a i)
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hS5 : S 5 = 28) (hS10 : S 10 = 36) :
    S 15 = 24 := by
  rcases ha with ⟨d, had⟩

  have h5_eq : S 5 = 5 * a 0 + 10 * d := by
    rw [hS 5]
    norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4]
    ring

  have h10_eq : S 10 = 10 * a 0 + 45 * d := by
    rw [hS 10]
    norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9]
    ring
  
  rw [h5_eq] at hS5
  rw [h10_eq] at hS10
  
  have h15_eq : S 15 = 15 * a 0 + 105 * d := by
    rw [hS 15]
    norm_num [Finset.sum_range_succ, had 1, had 2, had 3, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14]
    ring
  
  rw [h15_eq]

  linarith