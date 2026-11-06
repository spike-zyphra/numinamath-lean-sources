import Mathlib

theorem algebra_98798 (a : ℕ → ℝ) (ha : a 0 = 100) (h : ∀ n, a (n + 1) = a n - 50)
    (h' : 0 < a n) (h'' : 1 / 4 = 1 / (a 0 ^ 2)) :
    ∑' n, 1 / (a n ^ 2) = 1 / 2 := by
  have h3 : a 0 ^ 2 = 4 := by 
    have hne : a 0 ≠ 0 := by
      by_contra h0
      rw [h0] at h''
      norm_num at h''
    field_simp [hne] at h''
    nlinarith
  have h4 : a 0 = 100 := ha
  rw [h4] at h3
  nlinarith