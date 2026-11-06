import Mathlib

theorem number_theory_69656 (a : ℤ) : 6 ∣ a ^ 9 - a := by
  have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by 
    omega
  rcases h1 with (h | h | h | h | h | h)
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega
  · 
    have : a ^ 9 % 6 = a % 6 := by
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    have h2 : (a ^ 9 - a) % 6 = 0 := by 
      rw [Int.sub_emod]
      rw [this]
      simp [Int.sub_emod, h, pow_succ]
      all_goals omega
    omega