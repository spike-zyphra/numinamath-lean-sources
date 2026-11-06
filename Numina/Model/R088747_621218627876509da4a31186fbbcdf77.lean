import Mathlib

theorem algebra_150178 {a : ℕ → ℝ} {h : ∃ d, ∀ n, a n = a 0 + d * n}
    (h5 : ∑ i in Finset.range 5, a i = 28) (h10 : ∑ i in Finset.range 10, a i = 36) :
    ∑ i in Finset.range 15, a i = 24 := by
  rcases h with ⟨d, hd⟩
  have eq1 : ∑ i in Finset.range 5, a i = 5 * a 0 + 10 * d := by
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4]
    ring
  have eq2 : ∑ i in Finset.range 10, a i = 10 * a 0 + 45 * d := by
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4, hd 5, hd 6, hd 7, hd 8, hd 9]
    ring
  have eq3 : ∑ i in Finset.range 15, a i = 15 * a 0 + 105 * d := by
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4, hd 5, hd 6, hd 7, hd 8, hd 9, hd 10, hd 11, hd 12, hd 13, hd 14]
    ring
  rw [eq1] at h5
  rw [eq2] at h10
  have hd_eq : d = -4 / 5 := by 
    linarith
  have ha0 : a 0 = 36 / 5 := by 
    linarith [h5, hd_eq]
  rw [eq3]
  rw [ha0, hd_eq]
  norm_num