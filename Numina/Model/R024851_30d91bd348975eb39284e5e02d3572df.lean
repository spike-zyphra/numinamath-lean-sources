import Mathlib

theorem number_theory_7250 (n : ℤ) :
    (7 ∣ n ∧ ¬ 7^2 ∣ n) → ¬∃ a b, n = a^2 + b^2 := by
  intro h
  rcases h with ⟨h1, h2⟩
  rintro ⟨a, b, hn⟩
  have h3 : n % 7 = 0 := by
    omega
  have h4 : a ^ 2 % 7 = 0 ∨ a ^ 2 % 7 = 1 ∨ a ^ 2 % 7 = 2 ∨ a ^ 2 % 7 = 4 := by
    have h1 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
  have h5 : b ^ 2 % 7 = 0 ∨ b ^ 2 % 7 = 1 ∨ b ^ 2 % 7 = 2 ∨ b ^ 2 % 7 = 4 := by
    have h1 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod, Int.mul_emod]
      <;> omega
  have h6 : (a ^ 2 + b ^ 2) % 7 = 0 := by
    omega
  have h7 : a ^ 2 % 7 = 0 := by 
    omega
  have h8 : b ^ 2 % 7 = 0 := by 
    omega
  have h9 : 7 ∣ a := by
    by_contra h
    push_neg at h
    have h1 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.mul_emod, h1, Int.add_emod] at h7
      <;> omega
  have h10 : 7 ∣ b := by
    by_contra h
    push_neg at h
    have h1 : b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.mul_emod, h1, Int.add_emod] at h8
      <;> omega
  obtain ⟨k, hk⟩ := h9
  obtain ⟨l, hl⟩ := h10
  rw [hk, hl] at hn
  ring_nf at hn
  have h7pow2 : 49 ∣ n := by
    omega
  have h8 : ¬ 7 ^ 2 ∣ n := h2
  have h9 : 7 ^ 2 ∣ n := by
    omega
  contradiction