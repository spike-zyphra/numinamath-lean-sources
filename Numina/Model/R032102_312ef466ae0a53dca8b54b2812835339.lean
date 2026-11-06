import Mathlib


theorem number_theory_242932 :
    ¬∃ x y z : ℤ, Odd x ∧ Odd y ∧ Odd z ∧ (x + y)^2 + (x + z)^2 = (y + z)^2 := by 
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  have hx1 : x % 2 = 1 := by
    rcases hx with ⟨a, ha⟩
    omega
  have hy1 : y % 2 = 1 := by
    rcases hy with ⟨b, hb⟩
    omega
  have hz1 : z % 2 = 1 := by
    rcases hz with ⟨c, hc⟩
    omega

  have eq1 : ((x + y) ^ 2 + (x + z) ^ 2 - (y + z) ^2) = 0 := by
    linarith

  have h3 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
    have hx4 : x % 2 = 1 := by
      rcases hx with ⟨a, ha⟩
      omega
    omega

  have h6 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by
    have hy4 : y % 2 = 1 := by
      rcases hy with ⟨b, hb⟩
      omega
    omega

  have h9 : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by
    have hz4 : z % 2 = 1 := by
      rcases hz with ⟨c, hc⟩
      omega
    omega

  have eq3 : ((x + y) ^ 2 + (x + z) ^ 2 - (y + z) ^2) % 8 = 0 := by 
    omega

  rcases h3 with h3 | h3 | h3 | h3 <;> rcases h6 with h6 | h6 | h6 | h6 <;> rcases h9 with h9 | h9 | h9 | h9 <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h3, h6, h9, Int.emod] at eq3 <;> omega