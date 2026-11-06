import Mathlib

theorem number_theory_2821
    (a b : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (m : ℤ)
    (hm : m = a * b * (a + b)) :
    Even m := by 
  rw [hm]
  -- may not need to split into cases
  -- can assume that a,b are even or odd
  have h1 : (a * b * (a + b)) % 2 = 0 := by 
    have h2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have h3 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    · -- case a even
      rcases h3 with (h3 | h3)
      · -- case b even
        simp [Int.mul_emod, Int.add_emod, h2, h3]
        all_goals omega
      · -- case b odd 
        simp [Int.mul_emod, Int.add_emod, h2, h3]
        all_goals omega
    · -- case a odd 
      rcases h3 with (h3 | h3)
      · -- case b even 
        simp [Int.mul_emod, Int.add_emod, h2, h3]
        all_goals omega
      · -- case b odd 
        simp [Int.mul_emod, Int.add_emod, h2, h3]
        all_goals omega 
  exact ⟨(a * b * (a + b)) / 2, by omega⟩