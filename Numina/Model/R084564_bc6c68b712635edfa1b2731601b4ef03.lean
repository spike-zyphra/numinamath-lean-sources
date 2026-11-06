import Mathlib

theorem algebra_218919 {x y : ℤ} (h : x * y = x + y) :
    (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 2) := by
  have h1 : x * y - x - y = 0 := by linarith 
  have h2 : (x - 1) * (y - 1) = 1 := by 
    linarith [h1]
  have h3 : (x - 1) = 1 ∨ (x - 1) = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h2
  cases h3 with
  | inl h4 =>
    have hx1 : x = 2 := by linarith 
    have hy1 : (y - 1) = 1 := by
      rw [h4] at h2 
      norm_num at h2 ⊢ 
      all_goals 
        linarith 
    have hy2 : y = 2 := by linarith 
    right 
    exact ⟨hx1, hy2⟩ 
  | inr h4 => 
    have hx2 : x = 0 := by linarith 
    have hy1 : (y - 1) = -1 := by 
      rw [h4] at h2 
      norm_num at h2 ⊢ 
      all_goals 
        linarith 
    have hy2 : y = 0 := by linarith 
    left 
    exact ⟨hx2, hy2⟩