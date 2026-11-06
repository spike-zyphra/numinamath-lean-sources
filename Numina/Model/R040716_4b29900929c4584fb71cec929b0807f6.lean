import Mathlib

theorem number_theory_136148 (k : ℤ) :
    ¬∃ n, n^3 = 1967 * k + 3 := by
  rintro ⟨n, hn⟩
  have h1 : n^3 % 7 = 0 ∨ n^3 % 7 = 1 ∨ n^3 % 7 = 6 := by
    have h2 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h) <;> 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : (1967 * k + 3) % 7 = 3 := by
    have h3 : (1967 * k) % 7 = 0 := by
      simp [Int.mul_emod, show (1967 : ℤ) % 7 = 0 by norm_num]
    omega
  have h3 : n^3 % 7 = 3 := by
    omega
  omega