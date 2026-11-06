import Mathlib

theorem algebra_137995 (a b : ℕ) (h : a^3 + a + 4 * b^2 = 4 * a * b + b + b * a^2) : a = b := by 
  have eq1 : a^3 + a + 4 * b^2 = 4 * a * b + b + b * a^2 := by
    linarith

  have eq3 : (a : ℤ) ^ 3 + (a : ℤ) + 4 * (b : ℤ) ^ 2 = 4 * (a : ℤ) * (b : ℤ) + (b : ℤ) + (b : ℤ) * (a : ℤ) ^ 2 := by 
    exact_mod_cast h 
  have eq4 : (a - (b : ℤ)) * ((a : ℤ) ^ 2 - 4 * (b : ℤ) + 1) = 0 := by 
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ)), sq_nonneg ((a : ℤ) - 2), sq_nonneg ((b : ℤ) - 2)]
  have eq5 : (a - (b : ℤ)) = 0 ∨ ((a : ℤ) ^ 2 - 4 * (b : ℤ) + 1) = 0 := by 
    cases (mul_eq_zero.mp eq4) with 
    | inl h6 => left; linarith 
    | inr h7 => right; linarith 
  cases eq5 with 
  | inl h6 => 
    have h7 : (a : ℤ) = (b : ℤ) := by linarith 
    have h8 : a = b := by 
      exact_mod_cast h7 
    exact_mod_cast h8 
  | inr h7 => 
    have eq6 : (a : ℤ) ^ 2 - 4 * (b : ℤ) + 1 = 0 := by 
      linarith 
    have eq7 : (a : ℤ) ^ 2 = 4 * (b : ℤ) - 1 := by 
      linarith 
    have eq8 : (a : ℤ) % 4 = 0 ∨ (a : ℤ) % 4 = 1 ∨ (a : ℤ) % 4 = 2 ∨ (a : ℤ) % 4 = 3 := by 
      omega 
    have eq9 : ((a : ℤ) ^ 2 : ℤ) % 4 = 3 := by 
      have eq10 : (a : ℤ) ^ 2 = 4 * (b : ℤ) - 1 := eq7 
      omega 
    have eq10 : ((a : ℤ) ^ 2 : ℤ) % 4 = 0 ∨ ((a : ℤ) ^ 2 : ℤ) % 4 = 1 := by 
      rcases eq8 with (h8 | h8 | h8 | h8) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h8, Int.sub_emod]
    omega