import Mathlib

theorem number_theory_125499: IsGreatest {n : ℕ | ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, n = a9 + a10 ∧
0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧
  a8 < a9 ∧ a9 < a10 ∧ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 = 102} 66 ∧
  IsLeast {n : ℕ | ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, n = a1 + a2 ∧
0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧
  a8 < a9 ∧ a9 < a10 ∧ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 = 102} 3 := by
  constructor 
  · -- Prove that 66 is greatest in the first set 
    constructor 
    · -- Show that 66 is achievable 
      use 1, 2, 3, 4, 5, 6, 7, 8, 32, 34 
      all_goals norm_num 
    · -- Show that 66 is greatest 
      intro n hn 
      rcases hn with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, 
        h_eq1, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ 
      have h10 : a1 ≥ 1 := by linarith 
      have h2' : a2 ≥ 2 := by 
        omega 
      have h3' : a3 ≥ 3 := by 
        omega 
      have h4' : a4 ≥ 4 := by 
        omega 
      have h5' : a5 ≥ 5 := by 
        omega 
      have h6' : a6 ≥ 6 := by 
        omega 
      have h7' : a7 ≥ 7 := by 
        omega 
      have h8' : a8 ≥ 8 := by 
        omega 
      have h10' : a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 ≥ 36 := by 
        linarith [h10, h2', h3', h4', h5', h6', h7', h8']
      have h14 : a9 + a10 ≤ 66 := by 
        omega 
      linarith [h_eq1, h14] 
  · -- Prove that 3 is least in the second set 
    constructor 
    · -- Show that 3 is achievable 
      use 1, 2, 3, 4, 5, 6, 7, 8, 32, 34 
      all_goals norm_num 
    · -- Show that 3 is minimum 
      intro n hn 
      rcases hn with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, 
        h_eq, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ 
      have h10 : a1 ≥ 1 := by linarith 
      have h2' : a2 ≥ 2 := by 
        omega 
      linarith [h_eq, h10, h2']