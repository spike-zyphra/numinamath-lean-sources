import Mathlib

theorem number_theory_204360 (a b c : ℤ) (ha : ∃ m, a = m^2) (hb : ∃ n, b = n^2)
    (hc : ∃ p, c = p^2) (h : 9 ∣ (a + b + c)) : 9 ∣ a - b ∨ 9 ∣ a - c ∨ 9 ∣ b - c := by
  rcases ha with ⟨m, ha⟩
  rcases hb with ⟨n, hb⟩
  rcases hc with ⟨p, hc⟩
  have h1 : (m ^ 2 + n ^ 2 + p ^ 2 : ℤ) % 9 = 0 := by 
    omega 
  have h2 : m ^ 2 % 9 = 0 ∨ m ^ 2 % 9 = 1 ∨ m ^ 2 % 9 = 4 ∨ m ^ 2 % 9 = 7 := by
    have h1 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_two, Int.add_emod, Int.mul_emod]
  have h3 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
    have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_two, Int.add_emod, Int.mul_emod]
  have h4 : p ^ 2 % 9 = 0 ∨ p ^ 2 % 9 = 1 ∨ p ^ 2 % 9 = 4 ∨ p ^ 2 % 9 = 7 := by 
    have h1 : p % 9 = 0 ∨ p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 3 ∨ p % 9 = 4 ∨ p % 9 = 5 ∨ p % 9 = 6 ∨ p % 9 = 7 ∨ p % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_two, Int.add_emod, Int.mul_emod]
  have h9 : 9 ∣ a - b ∨ 9 ∣ a - c ∨ 9 ∣ b - c := by
    by_contra h'
    push_neg at h'
    have h6 : ¬ (9 ∣ a - b) := h'.1
    have h7 : ¬ (9 ∣ a - c) := h'.2.1
    have h8 : ¬ (9 ∣ b - c) := h'.2.2
    have h9 : a % 9 ≠ b % 9 := by
      by_contra h10
      have h11 : 9 ∣ a - b := by
        omega
      contradiction
    have h10 : a % 9 ≠ c % 9 := by
      by_contra h11
      have h12 : 9 ∣ a - c := by
        omega
      contradiction
    have h11 : b % 9 ≠ c % 9 := by 
      by_contra h12
      have h13 : 9 ∣ b - c := by
        omega
      contradiction
    omega
  exact h9