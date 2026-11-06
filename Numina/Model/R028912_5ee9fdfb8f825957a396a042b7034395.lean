import Mathlib

theorem number_theory_11824 : IsLeast {b : ℕ | 0 < b ∧ ∃ a, 0 < a ∧ a - b = 6 ∧ Nat.gcd ((a ^ 3 + b ^ 3) / (a + b)) (a * b) = 9} 3 := by
  constructor 
  · -- Show 3 is in the set
    constructor
    · norm_num
    · use 9
      all_goals norm_num
  · -- Show no smaller element is in the set
    intro b hb
    rcases hb with ⟨hb1, a, ha1, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : b = 1 ∨ b = 2 := by 
      omega 
    rcases h3 with (h3 | h3)
    · -- b = 1
      have ha : a = 7 := by
        omega
      rw [ha, h3] at h2 
      norm_num at h2 
    · -- b = 2
      have ha : a = 8 := by 
        omega 
      rw [ha, h3] at h2
      norm_num at h2