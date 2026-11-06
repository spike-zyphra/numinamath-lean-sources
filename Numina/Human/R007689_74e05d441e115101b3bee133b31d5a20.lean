import Mathlib

set_option maxRecDepth 400000
/-For how many positive integers n ≤ 100 is it true that
10n has exactly three times as many positive divisors as n has?-/
theorem number_theory_609925: {n: ℕ | 1 ≤ n ∧ n ≤ 100 ∧ (Nat.divisors (10 * n)).card = 3 * (Nat.divisors (n)).card}.encard = 28 := by

-- we directly compute the set
  have h_eq:
  {n: ℕ | 1 ≤ n ∧ n ≤ 100 ∧ (Nat.divisors (10 * n)).card = 3 * (Nat.divisors (n)).card}
  ={2, 6, 14, 18, 22, 26, 34, 38, 42, 46, 54, 58, 62, 66, 74, 78, 82, 86, 94, 98,5, 15, 35, 45, 55, 65, 85, 95} := by
    ext n
    constructor
    -- the forward direction
    . intro h
      simp at h
      rcases h with ⟨h1,h2,h⟩
      simp
      by_contra! f
      interval_cases n
      all_goals absurd h; try native_decide
      all_goals absurd f; omega

    -- the backward direction
    . intro h
      simp
      simp at h
      rcases h with h | h | h | h | h | h | h | h | h | h
       | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals simp[h]; try omega
      all_goals native_decide

-- count the simplfied set
  rw [h_eq]
  simp [Set.encard]