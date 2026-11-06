import Mathlib

/- What is the smallest positive integer with remainder $2,3,4$ when divided by $3,5,7$ respectively? -/
theorem number_theory_610021 :
    IsLeast {n : ℕ | n > 0 ∧ n % 3 = 2 ∧ n % 5 = 3 ∧ n % 7 = 4} 53 := by
  -- We first show that 53 is a solution
  constructor
  . simp
  -- Now we show that any positive integer n with remainder 2, 3, 4 when divided by 3, 5, 7 respectively is ≥ 53
  intro n ⟨hn, h₁, h₂, h₃⟩
  -- We have n = 3x + 2, n = 5y + 3, n = 7z + 4 for some x, y, z
  have ⟨x, hx⟩ : ∃ x : ℕ, n = 3 * x + 2 := by
    use n / 3
    rw [← h₁]
    exact (Nat.div_add_mod n 3).symm
  have ⟨y, hy⟩ : ∃ y : ℕ, n = 5 * y + 3 := by
    use n / 5
    rw [← h₂]
    exact (Nat.div_add_mod n 5).symm
  have ⟨z, hz⟩ : ∃ z : ℕ, n = 7 * z + 4 := by
    use n / 7
    rw [← h₃]
    exact (Nat.div_add_mod n 7).symm
  -- So 3 ∣ 2 * n - 1, 5 ∣ 2 * n - 1, 7 ∣ 2 * n - 1
  have k₁ : 3 ∣ 2 * n - 1 := ⟨2 * x + 1, by rw [hx]; omega⟩
  have k₂ : 5 ∣ 2 * n - 1 := ⟨2 * y + 1, by rw [hy]; omega⟩
  have k₃ : 7 ∣ 2 * n - 1 := ⟨2 * z + 1, by rw [hz]; omega⟩
  -- So their least common multiple, 105, divides 2 * n - 1
  have k : Nat.lcm (Nat.lcm 3 5) 7 ∣ 2 * n - 1 := Nat.lcm_dvd (Nat.lcm_dvd k₁ k₂) k₃
  simp [Nat.lcm] at k
  -- So 2 * n - 1 ≥ 105 and n ≥ 53
  clear * - hn k
  omega
