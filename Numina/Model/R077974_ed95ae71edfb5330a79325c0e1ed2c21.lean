import Mathlib

theorem algebra_272496 {f : ℕ → ℤ} (h2 : f 2 = 5) (h3 : f 3 = 7)
    (h : ∀ m n, 0 < m → 0 < n → f m + f n = f (m * n)) :
    f 12 = 17 := by
  have h4 : f 4 = 10 := by
    specialize h 2 2 (by norm_num) (by norm_num)
    norm_num [h2] at h ⊢
    linarith
  have h12 : f 12 = 17 := by
    specialize h 4 3 (by norm_num) (by norm_num)
    norm_num [h4, h3] at h ⊢
    linarith
  exact h12