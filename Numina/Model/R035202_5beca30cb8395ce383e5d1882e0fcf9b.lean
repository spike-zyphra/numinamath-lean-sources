import Mathlib

theorem number_theory_189538: 
    { (x,y) : ℤ × ℤ | 19 * x ^ 3 - 84 * y ^ 2 = 1984 } = ∅ := by
  ext ⟨x, y⟩ 
  simp 
  intro h
  have eq1 : x ^ 3 % 7 = 0 ∨ x ^ 3 % 7 = 1 ∨ x ^ 3 % 7 = 6 := by 
    have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have eq2 : (19 * x ^ 3 : ℤ) % 7 = (5 * (x ^ 3 % 7) : ℤ) % 7 := by
    simp [Int.add_emod, Int.mul_emod]
    <;> omega
  have eq3 : (1984 : ℤ) % 7 = 3 := by
    norm_num
  have eq4 : (19 * x ^ 3 : ℤ) % 7 = 3 := by
    have h1 : (19 * x ^ 3 - 84 * y ^ 2 : ℤ) = 1984 := by linarith 
    omega 
  -- Multiply by 3 (inverse of 5 mod 7) to get x^3 ≡ 2 mod 7
  have eq5 : (5 * (x ^ 3 % 7) : ℤ) % 7 = 3 := by 
    omega 
  rcases eq1 with (hx | hx | hx) 
  · 
    rw [hx] at eq5
    omega
  · 
    rw [hx] at eq5
    omega 
  · 
    rw [hx] at eq5 
    omega 
  all_goals omega