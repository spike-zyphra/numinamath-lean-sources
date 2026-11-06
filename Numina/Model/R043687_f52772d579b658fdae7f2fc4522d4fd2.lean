import Mathlib

theorem number_theory_259120 (n : ℤ) (hn : n > 0) :
    24 ∣ n^4 + 2 * n^3 + 11 * n^2 + 10 * n := by
  have h1 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    omega
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  have h3 : (n ^ 4 + 2 * n^3 + 11 * n ^ 2 + 10 * n) % 8 = 0 := by 
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h, Int.sub_emod]
  have h4 : (n ^ 4 + 2 * n^3 + 11 * n ^ 2 + 10 * n) % 3 = 0 := by
    rcases h2 with (h | h | h) <;> simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h, Int.sub_emod]
  -- From h3 and h4 we can conclude that $24 | n^4 + 2n^3 + 11n^2 + 10n$ using the omega tactic
  have h5 : 24 ∣ (n ^ 4 + 2 * n^3 + 11 * n ^ 2 + 10 * n) := by 
    omega
  exact h5