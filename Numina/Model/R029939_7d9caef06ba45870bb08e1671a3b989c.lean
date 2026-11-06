import Mathlib

theorem algebra_20877 (d : ℕ → ℝ) (h₀ : d 0 = 45) (h₁ : ∀ n, d (n + 1) = d n - 5) :
    ∑ i in Finset.range 9, d i = 225 := by
  have h2 : d 1 = 40 := by
    specialize h₁ 0
    rw [h₀] at h₁
    norm_num at h₁ ⊢
    linarith
  have h3 : d 2 = 35 := by
    specialize h₁ 1
    rw [h2] at h₁
    norm_num at h₁ ⊢
    linarith
  have h4 : d 3 = 30 := by
    specialize h₁ 2
    rw [h3] at h₁
    norm_num at h₁ ⊢
    linarith
  have h5 : d 4 = 25 := by
    specialize h₁ 3
    rw [h4] at h₁
    norm_num at h₁ ⊢
    linarith
  have h6 : d 5 = 20 := by
    specialize h₁ 4
    rw [h5] at h₁
    norm_num at h₁ ⊢
    linarith
  have h7 : d 6 = 15 := by
    specialize h₁ 5
    rw [h6] at h₁
    norm_num at h₁ ⊢
    linarith
  have h8 : d 7 = 10 := by
    specialize h₁ 6
    rw [h7] at h₁
    norm_num at h₁ ⊢
    linarith
  have h9 : d 8 = 5 := by
    specialize h₁ 7
    rw [h8] at h₁
    norm_num at h₁ ⊢
    linarith
  norm_num [Finset.sum_range_succ, h₀, h2, h3, h4, h5, h6, h7, h8, h9]