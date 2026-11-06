import Mathlib

theorem number_theory_197115 (n : ℕ) :
    ¬ ∃ m, m^2 = ∑ i ∈ Finset.range 5, (n + i)^2 := by
  rintro ⟨m, hm⟩
  norm_num [Finset.sum_range_succ] at hm
  have h1 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega 
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
  have h2 : (n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 + (n + 4) ^ 2) % 4 = 2 ∨ (n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 + (n + 4) ^ 2) % 4 = 3 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega 
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
      simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h2]
  have h3 : m ^ 2 % 4 = (n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 + (n + 4) ^ 2) % 4 := by 
    have h4 : m ^ 2 = n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2 + (n + 4) ^ 2 := by 
      omega 
    omega 
  rcases h2 with (h | h)
  · -- Case: sum side ≡ 2
    omega 
  · -- Case: sum side ≡ 3
    omega