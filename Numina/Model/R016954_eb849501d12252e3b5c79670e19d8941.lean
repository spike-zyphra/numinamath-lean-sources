import Mathlib

theorem number_theory_7843 : ¬∃ m n : ℤ, m > 0 ∧ n > 0 ∧ 19^19 = m^3 + n^4 := by

  rintro ⟨m, n, hm, hn, heq⟩
  have h1 := congr_arg (fun x => x % 13) heq
  norm_num at h1
  have h2 : m^3 % 13 = 0 ∨ m^3 % 13 = 1 ∨ m^3 % 13 = 5 ∨ m^3 % 13 = 8 ∨ m^3 % 13 = 12 := by
    have h1 : m % 13 = 0 ∨ m % 13 = 1 ∨ m % 13 = 2 ∨ m % 13 = 3 ∨ m % 13 = 4 ∨ m % 13 = 5 ∨ m % 13 = 6 ∨ m % 13 = 7 ∨ m % 13 = 8 ∨ m % 13 = 9 ∨ m % 13 = 10 ∨ m % 13 = 11 ∨ m % 13 = 12 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] 
  have h3 : n^4 % 13 = 0 ∨ n^4 % 13 = 1 ∨ n^4 % 13 = 3 ∨ n^4 % 13 = 9 := by
    have h1 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] 
  omega