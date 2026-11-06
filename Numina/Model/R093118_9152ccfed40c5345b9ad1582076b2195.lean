import Mathlib

theorem number_theory_222618 (n : ℤ) : 120 ∣ n * (n^2 - 1) * (n^2 - 5 * n + 26) := by
  have h1 : n * (n^2 - 1) * (n^2 - 5 * n + 26) % 8 = 0 := by
    have h2 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h)
    · -- n ≡ 0 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 1 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 2 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 3 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 4 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 5 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 6 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 7 (mod 8)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega

  have h3 : n * (n^2 - 1) * (n^2 - 5 * n + 26) % 3 = 0 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h | h | h)
    · -- n ≡ 0 (mod 3)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 1 (mod 3)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 2 (mod 3)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega

  have h5 : n * (n^2 - 1) * (n^2 - 5 * n + 26) % 5 = 0 := by
    have h6 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h6 with (h | h | h | h | h)
    · -- n ≡ 0 (mod 5)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 1 (mod 5)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 2 (mod 5)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 3 (mod 5)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega
    · -- n ≡ 4 (mod 5)
      simp [h, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.add_emod] 
      <;> omega

  omega