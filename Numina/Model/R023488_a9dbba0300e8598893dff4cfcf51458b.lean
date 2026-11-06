import Mathlib

theorem number_theory_301624 : ¬(∃ n, n^2 = 2^2017) := by
  intro h
  rcases h with ⟨n, hn⟩
  have h1 : n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
    have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h1 with (h | h | h)
    · -- n % 3 = 0
      simp [pow_two, Nat.mul_mod, h]
    · -- n % 3 = 1
      simp [pow_two, Nat.mul_mod, h]
    · -- n % 3 = 2
      simp [pow_two, Nat.mul_mod, h]
  
  have h2 : (2 ^ 2017) % 3 = 2 := by
    norm_num
  
  have h3 : n ^ 2 % 3 = 2 := by
    omega
  
  omega