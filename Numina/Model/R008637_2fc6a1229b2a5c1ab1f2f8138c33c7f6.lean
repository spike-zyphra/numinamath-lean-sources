import Mathlib
open Real

theorem algebra_95691 {S : ℕ → ℤ} (hS : ∀ n, S (n + 2) = S n + S (n + 1)) (hS9 : S 9 = 110) (hS7 : S 7 = 42) :
S 4 = 10 := by 
  have h1 : S 9 = S 7 + S 8 := by 
    specialize hS 7
    norm_num at hS ⊢
    linarith 
  rw [hS9, hS7] at h1 
  have hS8 : S 8 = 68 := by linarith 
  have h2 : S 8 = S 6 + S 7 := by 
    specialize hS 6 
    norm_num at hS ⊢
    linarith 
  rw [hS8, hS7] at h2 
  have hS6 : S 6 = 26 := by linarith 
  have h3 : S 7 = S 5 + S 6 := by 
    specialize hS 5 
    norm_num at hS ⊢
    linarith 
  rw [hS7, hS6] at h3 
  have hS5 : S 5 = 16 := by linarith 
  have h4 : S 6 = S 4 + S 5 := by 
    specialize hS 4 
    norm_num at hS ⊢
    linarith 
  rw [hS6, hS5] at h4 
  linarith