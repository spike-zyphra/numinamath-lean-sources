import Mathlib

theorem number_theory_605636 (x y : ℤ) (h₁ : ∃ n, n^2 = 5 * x + 6 * y) (h₂ : ∃ m, m^2 = 6 * x + 5 * y) :
    11 ∣ x ∧ 11 ∣ y := by
  rcases h₁ with ⟨n, hn⟩
  rcases h₂ with ⟨m, hm⟩
  have h3 : n^2 + m^2 = 11 * (x + y) := by
    linarith [hn, hm]
  have h4 : n^2 % 11 = 0 ∨ n^2 % 11 = 1 ∨ n^2 % 11 = 3 ∨ n^2 % 11 = 4 ∨ n^2 % 11 = 5 ∨ n^2 % 11 = 9 := by
    have h11 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod]
  have h5 : m^2 % 11 = 0 ∨ m^2 % 11 = 1 ∨ m^2 % 11 = 3 ∨ m^2 % 11 = 4 ∨ m^2 % 11 = 5 ∨ m^2 % 11 = 9 := by
    have h11 : m % 11 = 0 ∨ m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ m % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod]
  have h6 : (n^2 + m^2) % 11 = 0 := by
    omega
  have h7 : n^2 % 11 = 0 := by 
    omega
  have h8 : m^2 % 11 = 0 := by 
    omega
  have h9 : n % 11 = 0 := by
    have h11 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod] at h7 ⊢ <;> omega
  have h10 : m % 11 = 0 := by
    have h11 : m % 11 = 0 ∨ m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ m % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.add_emod] at h8 ⊢ <;> omega
  have h11 : ∃ k : ℤ, n = 11 * k := by
    refine' ⟨n / 11, by omega⟩
  have h12 : ∃ j : ℤ, m = 11 * j := by
    refine' ⟨m / 11, by omega⟩
  rcases h11 with ⟨k, hk⟩
  rcases h12 with ⟨j, hj⟩
  rw [hk] at hn
  rw [hj] at hm
  have h13 : 11 ∣ x + y := by
    ring_nf at hn hm
    omega
  have h14 : x % 11 = 0 := by
    ring_nf at hn hm
    omega
  have h15 : y % 11 = 0 := by
    ring_nf at hn hm
    omega
  exact ⟨by omega, by omega⟩