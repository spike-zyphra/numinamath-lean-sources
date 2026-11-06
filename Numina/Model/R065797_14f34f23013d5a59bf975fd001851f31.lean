import Mathlib
open Real

theorem algebra_96157 (M F : ℕ) (heq : M * 58 + F * 26 = 136 * 100) (hf : F * (58 + 26) = 64 * 100) (ht : M + F = 200) : (M : ℝ) / (M + F) * 100 = 75 := by 
  have h1 : F * 84 = 6400 := by
    nlinarith
  have h2 : F ≤ 76 := by
    omega
  have h3 : F ≥ 76 := by 
    omega
  have h4 : F = 76 := by 
    omega
  nlinarith