import Mathlib

-- Letters A, B, C, and D represent four different digits selected from 0, 1, 2, …, 9. If (A+B)/(C+D) is an integer that is as large as possible, what is the value of A+B? (A) 13 (B) 14 (C) 15 (D) 16 (E) 17
theorem number_theory_93724 : IsGreatest {E | ∃ (A B C D:ℕ), A ≤ 9 ∧ B ≤ 9 ∧ C ≤ 9 ∧ D ≤ 9 ∧ A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧ ∃ (m : ℕ), m = ((A+B):ℚ)/(C+D) ∧ E = A + B} 17 := by 
  constructor 
  · -- Show 17 is in the set
    use 9, 8, 0, 1
    norm_num 
    all_goals 
      use 17 
      norm_num 
  · -- Show that 17 is greatest
    intro E h 
    rcases h with ⟨A, B, C, D, hA, hB, hC, hD, h1, h2, h3, h4, h5, h6, m, hm1, hm2⟩ 
    have h7 : E = A + B := by linarith [hm2]
    have h8 : A + B ≤ 17 := by
      have hA' : A ≤ 9 := hA 
      have hB' : B ≤ 9 := hB 
      omega
    have hE : E ≤ 17 := by 
      linarith [h7, h8] 
    linarith [hE]