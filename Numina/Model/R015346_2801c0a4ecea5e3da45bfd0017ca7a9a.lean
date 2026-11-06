import Mathlib

theorem number_theory_207751 (x y z : ℤ) (hx : Odd x) (hy : Odd y) (hz : Odd z)
    (h : (x - z) ^ 2 + (y - z) ^ 2 = (x + y) ^ 2) :
    False := by
  have h1 : x % 2 = 1 := by
    obtain ⟨k, hk⟩ := hx
    omega
  have h3 : y % 2 = 1 := by
    obtain ⟨k, hk⟩ := hy
    omega
  have h5 : z % 2 = 1 := by
    obtain ⟨k, hk⟩ := hz
    omega
  have eq1 : (x - z) ^ 2 + (y - z) ^ 2 = (x + y) ^ 2 := h
  have h10 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by 
    have h1' : x % 2 = 1 := h1
    omega
  have h11 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by 
    have h3' : y % 2 = 1 := h3
    omega
  have h12 : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by 
    have h5' : z % 2 = 1 := h5
    omega
  have eq1_mod8 : ((x - z) ^ 2 + (y - z) ^ 2) % 8 = ((x + y) ^ 2) % 8 := by
    omega
  rcases h10 with (h10 | h10 | h10 | h10) <;> rcases h11 with (h11 | h11 | h11 | h11) <;> rcases h12 with (h12 | h12 | h12 | h12) <;> norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h10, h11, h12] at eq1_mod8 
  <;> omega