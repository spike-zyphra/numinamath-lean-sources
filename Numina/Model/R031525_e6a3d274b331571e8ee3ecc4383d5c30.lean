import Mathlib

theorem number_theory_4986
    (n : ℤ)
    (h : Odd n) :
    ∃ k, n ^ 4 = 16 * k + 1 := by 
  have h1 : n % 2 = 1 := by 
    rcases h with ⟨m, hm⟩
    have : n = 2 * m + 1 := by linarith 
    rw [this] 
    omega 
  have h2 : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by 
    omega 
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2)
  · -- n ≡ 1 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 3 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 5 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 7 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 9 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 11 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 13 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega 
  · -- n ≡ 15 (mod 16)
    use (n ^ 4 - 1) / 16 
    have h3 : n ^ 4 % 16 = 1 := by 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod] 
    omega