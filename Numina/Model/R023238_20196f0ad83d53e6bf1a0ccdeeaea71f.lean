import Mathlib

theorem number_theory_300959 (a : ℤ) : ¬ ∃ n, n^2 = 1990 * a^12 + 6 := by
  rintro ⟨n, hn⟩
  have h1 : n^2 % 16 = 0 ∨ n^2 % 16 = 1 ∨ n^2 % 16 = 4 ∨ n^2 % 16 = 9 := by
    have h1 : n % 16 = 0 ∨ n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨ n % 16 = 11 ∨ n % 16 = 12 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h1]
  have h2 : (1990 * a^12 + 6) % 16 = 6 ∨ (1990 * a^12 + 6) % 16 = 12 := by
    have h5 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h5 with (h5 | h5)
    · -- Assume a is even.
      have h3 : a % 2 = 0 := h5
      have h4 : a % 16 = 0 ∨ a % 16 = 2 ∨ a % 16 = 4 ∨ a % 16 = 6 ∨ a % 16 = 8 ∨ a % 16 = 10 ∨ a % 16 = 12 ∨ a % 16 = 14 := by 
        omega 
      have h5 : (1990 * a^12 + 6) % 16 = 6 := by
        rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
          simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, Int.add_emod, Int.mul_emod, h4]
      left
      omega
    · -- Assume a is odd.
      have h3 : a % 2 = 1 := h5
      have h4 : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨ a % 16 = 13 ∨ a % 16 = 15 := by 
        omega 
      have h5 : (1990 * a^12 + 6) % 16 = 12 := by
        rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
          simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, Int.add_emod, Int.mul_emod, h4]
      right
      omega
  have h3 : n^2 % 16 = (1990 * a^12 + 6) % 16 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  all_goals
    omega