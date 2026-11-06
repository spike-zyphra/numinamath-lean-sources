import Mathlib

theorem number_theory_275828 (n : ℤ) (h₀ : Odd n) : 24 ∣ (n^3 - n) := by
  have h1 : n % 2 = 1 := by 
    rcases h₀ with ⟨k, hk⟩
    omega
  have h2 : (n^3 - n) % 24 = 0 := by
    have h4 : n % 24 = 1 ∨ n % 24 = 3 ∨ n % 24 = 5 ∨ n % 24 = 7 ∨ n % 24 = 9 ∨ n % 24 = 11 ∨ n % 24 = 13 ∨ n % 24 = 15 ∨ n % 24 = 17 ∨ n % 24 = 19 ∨ n % 24 = 21 ∨ n % 24 = 23 := by
      have h1 : n % 2 = 1 := by
        rcases h₀ with ⟨k, hk⟩
        omega
      omega
    rcases h4 with (h | h | h | h | h | h | h | h | h | h | h | h)
    · -- Case n % 24 = 1
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 3
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 5
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 7
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 9
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 11
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 13
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 15
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 17
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 19
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 21
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
    · -- Case n % 24 = 23
      simp [pow_succ, Int.sub_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
  exact Int.dvd_of_emod_eq_zero h2