import Mathlib

theorem number_theory_159235 : ¬ ∃ x y : ℤ, 2*x^3-7*y=1 := by
  rintro ⟨x, y, h⟩
  have h1 : (2 * x^3) % 7 = 1 % 7 := by 
    omega
  have h2 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
    omega
  rcases h2 with (h | h | h | h | h | h | h)
  · -- x ≡ 0 (mod 7)
    have h3 : x ^ 3 % 7 = 0 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 0 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 1 (mod 7)
    have h3 : x ^ 3 % 7 = 1 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 2 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 2 (mod 7)
    have h3 : x ^ 3 % 7 = 1 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 2 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 3 (mod 7)
    have h3 : x ^ 3 % 7 = 6 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 5 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 4 (mod 7)
    have h3 : x ^ 3 % 7 = 1 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 2 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 5 (mod 7)
    have h3 : x ^ 3 % 7 = 6 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 5 := by 
      simp [Int.mul_emod, h3]
    omega
  · -- x ≡ 6 (mod 7)
    have h3 : x ^ 3 % 7 = 6 := by
      simp [pow_succ, Int.mul_emod, h]
    have h4 : (2 * x^3) % 7 = 5 := by 
      simp [Int.mul_emod, h3]
    omega