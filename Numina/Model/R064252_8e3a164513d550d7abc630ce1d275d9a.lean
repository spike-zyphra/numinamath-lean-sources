import Mathlib

theorem algebra_100947 {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / 3 ^ (n - 1)) :
    ¬∃ S : ℕ → ℝ, (∀ n, S n = ∑ k in Finset.Icc 1 n, a k) ∧
      (∀ k, S (k + 1) = S k + 1 / 3 ^ (k + 1)) := by
  rintro ⟨S, h₁, h₂⟩
  have h3 : S 1 = 1 := by 
    specialize h₁ 1
    norm_num [Finset.sum_singleton, ha] at h₁ ⊢
    linarith
  have h4 : S 0 = 0 := by 
    specialize h₁ 0 
    norm_num [Finset.sum_eq_zero] at h₁ ⊢ 
    linarith 
  have h1 := h₂ 0 
  norm_num [h4] at h1 
  linarith [h3, h1]