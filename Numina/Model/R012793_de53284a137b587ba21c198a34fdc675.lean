import Mathlib

theorem number_theory_112639 : ∀ n : ℤ, ¬ 49 ∣ n^2 + 3 * n + 4 := by
  intro n 
  intro h
  have h4 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
  · -- n % 7 = 0
    have h5 : (n^2 + 3 * n + 4) % 7 = 4 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  · -- n % 7 = 1
    have h5 : (n^2 + 3 * n + 4) % 7 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  · -- n % 7 = 2
    have h5 : (n^2 + 3 * n + 4) % 7 = 0 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    -- Now check modulo 49
    have h6 : n % 7 = 2 := h4
    have h7 : n % 49 = 2 ∨ n % 49 = 9 ∨ n % 49 = 16 ∨ n % 49 = 23 ∨ n % 49 = 30 ∨ n % 49 = 37 ∨ n % 49 = 44 := by
      omega
    rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7)
    · -- n % 49 = 2
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 9
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 16
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 23
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 30
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 37
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
    · -- n % 49 = 44
      have h8 : (n^2 + 3 * n + 4) % 49 = 14 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h7, Int.ofNat]
      omega
  · -- n % 7 = 3
    have h5 : (n^2 + 3 * n + 4) % 7 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  · -- n % 7 = 4
    have h5 : (n^2 + 3 * n + 4) % 7 = 4 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  · -- n % 7 = 5
    have h5 : (n^2 + 3 * n + 4) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  · -- n % 7 = 6
    have h5 : (n^2 + 3 * n + 4) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega