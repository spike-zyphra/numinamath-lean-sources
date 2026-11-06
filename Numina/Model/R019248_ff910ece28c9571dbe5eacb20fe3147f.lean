import Mathlib

theorem algebra_220749 : ¬ ∃ n m : ℤ, n * (n + 1) * (n + 2) * (n + 3) + m ^ 5 = 5000 := by 
  rintro ⟨n, m, h⟩
  have h1 : n * (n + 1) * (n + 2) * (n + 3) + m ^ 5 = 5000 := h
  have h2 : (n * (n + 1) * (n + 2) * (n + 3) + m ^ 5) % 11 = 5000 % 11 := by
    omega
  have h3 : (n * (n + 1) * (n + 2) * (n + 3) + m ^ 5) % 11 = 6 := by
    norm_num at h2 ⊢
    omega
  have h4 : (n * (n + 1) * (n + 2) * (n + 3)) % 11 = 0 ∨ (n * (n + 1) * (n + 2) * (n + 3)) % 11 = 2 ∨ 
    (n * (n + 1) * (n + 2) * (n + 3)) % 11 = 4 ∨ (n * (n + 1) * (n + 2) * (n + 3)) % 11 = 8 ∨ 
    (n * (n + 1) * (n + 2) * (n + 3)) % 11 = 10 := by
    have h11 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ 
      n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ 
      n % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [Int.add_emod, Int.mul_emod, Int.sub_emod, h, pow_two, pow_succ, Int.add_emod, Int.mul_emod]
  have h5 : (m ^ 5) % 11 = 0 ∨ (m ^ 5) % 11 = 1 ∨ (m ^ 5) % 11 = 10 := by
    have h11 : m % 11 = 0 ∨ m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ 
      m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ 
      m % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod, h, Int.mul_emod, Int.add_emod]
  omega