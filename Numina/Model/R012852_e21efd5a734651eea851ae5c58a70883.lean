import Mathlib

theorem number_theory_7981 (n : ℤ) (h : n ≡ 4 [ZMOD 9]) :
    ¬∃ x y z : ℤ, x^3 + y^3 + z^3 = n := by
  rintro ⟨x, y, z, hn⟩
  have h4 : n % 9 = 4 := by 
    norm_num [Int.ModEq] at h
    omega
  have h1 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
    have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, 
          pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
    <;> omega 
  have h2 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by
    have h1 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, 
          pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
    <;> omega 
  have h3 : z^3 % 9 = 0 ∨ z^3 % 9 = 1 ∨ z^3 % 9 = 8 := by
    have h1 : z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, 
          pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
    <;> omega 
  have h4' : (x^3 + y^3 + z^3) % 9 = 4 := by
    omega 
  omega