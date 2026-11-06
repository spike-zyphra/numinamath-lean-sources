import Mathlib

open Nat

theorem number_theory_7720 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
  (h : ∃ n, n^2 = a * b + 1) :
  ∃ c : ℕ, 0 < c ∧ ∃ m, m^2 = a * c + 1 ∧ ∃ p, p^2 = b * c + 1 := by
  rcases h with ⟨n, hn⟩
  use a + b + 2 * n
  constructor 
  · -- Show c > 0
    nlinarith
  · -- Prove the existence of m and p
    use a + n
    constructor
    · -- Prove m^2  = a * c + 1
      have eq1 : (a + n) ^ 2 = a * (a + b + 2 * n) + 1 := by 
        nlinarith [hn]
      exact eq1
    · -- Prove existence of p
      use b + n
      all_goals 
      have eq2 : (b + n) ^ 2 = b * (a + b + 2 * n) + 1 := by 
        nlinarith [hn]
      exact eq2