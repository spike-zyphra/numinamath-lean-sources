import Mathlib

theorem number_theory_215214 : ¬∃ m n : ℤ, m ^ 2 + n ^ 2 = 1980 := by
  rintro ⟨m, n, h⟩

  have h1 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]

  have h2 : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2]

  have h3 : (m ^ 2 + n ^ 2) % 4 = 0 := by
    omega

  have h4 : m ^ 2 % 4 = 0 := by 
    omega

  have h5 : n ^ 2 % 4 = 0 := by 
    omega

  -- If m^2 % 4 = 0, then m is even
  have h6 : m % 2 = 0 := by
    by_contra h7
    push_neg at h7
    have h7 : m % 2 = 1 := by
      omega
    have h8 : m ^ 2 % 2 = 1 := by
      simp [pow_two, Int.mul_emod, h7]
    have h9 : m ^ 2 % 4 = 1 := by 
      have h9 : m % 4 = 1 ∨ m % 4 = 3 := by
        omega
      rcases h9 with (h9 | h9)
      <;> simp [pow_two, Int.add_emod, Int.mul_emod, h9]
    omega

  -- If n^2 % 4 = 0, then n is even
  have h12 : n % 2 = 0 := by
    by_contra h7
    push_neg at h7
    have h7 : n % 2 = 1 := by
      omega
    have h8 : n ^ 2 % 2 = 1 := by
      simp [pow_two, Int.mul_emod, h7]
    have h9 : n ^ 2 % 4 = 1 := by 
      have h9 : n % 4 = 1 ∨ n % 4 = 3 := by
        omega
      rcases h9 with (h9 | h9)
      <;> simp [pow_two, Int.add_emod, Int.mul_emod, h9]
    omega

  have h7 : ∃ a : ℤ, m = 2 * a := ⟨m / 2, by omega⟩

  have h8 : ∃ b : ℤ, n = 2 * b := ⟨n / 2, by omega⟩

  rcases h7 with ⟨a, ha⟩
  rcases h8 with ⟨b, hb⟩

  rw [ha] at h
  rw [hb] at h

  have h9 : 4 * (a ^ 2 + b ^ 2) = 1980 := by 
    nlinarith

  have h10 : a ^ 2 + b ^ 2 = 495 := by
    nlinarith

  have h11 : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
    have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]

  have h12 : b ^ 2 % 8 = 0 ∨ b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by 
    have h2 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h2]

  have h13 : (a ^ 2 + b ^ 2) % 8 = 7 := by
    omega

  omega