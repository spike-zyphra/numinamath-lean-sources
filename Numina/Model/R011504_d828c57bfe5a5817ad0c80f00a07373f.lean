import Mathlib

theorem number_theory_624904 : Set.encard {(x, y) : ℤ × ℤ | x ^ 2 - y ^ 2 = 1991} = 8 := by
  have h1 : {(x, y) : ℤ × ℤ | x ^ 2 - y ^ 2 = 1991} = { 
    (996, 995), (96, 85), (96, -85), (996, -995), 
    (-996, -995), (-96, -85), (-96, 85), (-996, 995) 
  } := by 
    ext ⟨x, y⟩
    simp 
    constructor 
    · -- Assume (x, y) is a solution
      rintro H
      have h_eq : x ^ 2 - y ^ 2 = 1991 := by
        omega 
      have h_eq2 : (x - y) * (x + y) = 1991 := by
        nlinarith 
      have h1 : (x - y) ∣ 1991 := by 
        use x + y 
        all_goals 
          linarith [h_eq2]
      have h7 : (x - y) = 1 ∨ (x - y) = 11 ∨ (x - y) = 181 ∨ (x - y) = 1991 ∨ 
        (x - y) = -1 ∨ (x - y) = -11 ∨ (x - y) = -181 ∨ (x - y) = -1991 := by
        have h8 : (x - y) ∣ 1991 := h1
        have h9 : (x - y) ≤ 1991 := by 
          exact Int.le_of_dvd (by norm_num) h8 
        have h9a : (x - y) ≥ -1991 := by 
          have h4 : -(x - y) ∣ 1991 := by 
            exact Int.neg_dvd.2 h8 
          have h10 : -(x - y) ≤ 1991 := by 
            exact Int.le_of_dvd (by norm_num) h4 
          omega 
        interval_cases h3 : (x - y) <;> norm_num at h8 ⊢ 
        <;> try { tauto }
      rcases h7 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8)
      · -- x - y = 1 
        have h10 : x + y = 1991 := by 
          rw [h8] at h_eq2
          nlinarith
        have hx : x = 996 := by
          omega
        have hy : y = 995 := by 
          omega
        simp [hx, hy]
      · -- x - y = 11 
        have h10 : x + y = 181 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = 96 := by
          omega
        have hy : y = 85 := by 
          omega 
        simp [hx, hy]
      · -- x - y = 181 
        have h10 : x + y = 11 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = 96 := by
          omega
        have hy : y = -85 := by 
          omega 
        simp [hx, hy]
      · -- x - y = 1991 
        have h10 : x + y = 1 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = 996 := by
          omega
        have hy : y = -995 := by 
          omega 
        simp [hx, hy]
      · -- x - y = -1 
        have h10 : x + y = -1991 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = -996 := by
          omega
        have hy : y = -995 := by 
          omega 
        simp [hx, hy]
      · -- x - y = -11 
        have h10 : x + y = -181 := by 
          rw [h8] at h_eq2
          nlinarith 
        have hx : x = -96 := by
          omega
        have hy : y = -85 := by 
          omega 
        simp [hx, hy]
      · -- x - y = -181 
        have h10 : x + y = -11 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = -96 := by
          omega
        have hy : y = 85 := by 
          omega 
        simp [hx, hy]
      · -- x - y = -1991 
        have h10 : x + y = -1 := by 
          rw [h8] at h_eq2 
          nlinarith 
        have hx : x = -996 := by
          omega
        have hy : y = 995 := by 
          omega 
        simp [hx, hy]
    · -- Show the right side implies the left side 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
      · norm_num 
      · norm_num 
      · norm_num
      · norm_num
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals omega