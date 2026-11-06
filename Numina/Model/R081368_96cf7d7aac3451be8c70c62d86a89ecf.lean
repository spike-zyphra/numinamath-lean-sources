import Mathlib

theorem number_theory_215981 (n : ℕ) (h₀ : n < 1000) :
    7 ∣ (n + 523000) ∧ 8 ∣ (n + 523000) ∧ 9 ∣ (n + 523000) ↔
    n = 152 ∨ n = 656 := by 
  constructor
  · -- Forward direction: if 7, 8, and 9 all divide n + 523000, then n is either 152 or 656
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : n < 1000 := h₀
    interval_cases n <;> omega 
  · -- Backward direction: if n is either 152 or 656, then 7, 8, and 9 all divide n + 523000
    rintro (h | h)
    · -- Case n = 152
      rw [show n = 152 by linarith]
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- Case n = 656
      rw [show n = 656 by linarith]
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num