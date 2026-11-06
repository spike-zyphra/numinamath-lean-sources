import Mathlib

theorem number_theory_157699 (s1 s2 s3 : Finset ℕ)
    (h₀ : s1 ⊆ Finset.Icc 10 19) (h₁ : s2 ⊆ Finset.Icc 90 99)
    (h₂ : s1.card = 5) (h₃ : s2.card = 5) (h₄ : s3 = s1 ∪ s2)
    (h₅ : ∀ x ∈ s3, ∀ y ∈ s3, |(x : ℤ) - y| % 10 ≠ 0) :
    ∑ x ∈ s3, x = 545 := by
  have h12 : s1.Nonempty := by 
    apply Finset.card_pos.mp 
    rw [h₂]
    norm_num 
  rcases h12 with ⟨x, hx⟩ 
  have h13 : x ∈ s3 := by
    rw [h₄]
    simp at *
    all_goals 
      try { 
        tauto 
      }
  have h14 : |(x : ℤ) - x| % 10 = 0 := by 
    norm_num 
  have h15 : |(x : ℤ) - x| % 10 ≠ 0 := h₅ x (show x ∈ s3 by 
    rw [h₄]
    simp at *
    all_goals try tauto 
  ) x (show x ∈ s3 by 
    rw [h₄]
    simp at *
    all_goals try tauto 
  )
  contradiction