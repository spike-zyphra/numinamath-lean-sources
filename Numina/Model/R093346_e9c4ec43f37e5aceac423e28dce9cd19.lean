import Mathlib

theorem number_theory_126614 (k : ℕ) (hk : 0 < k) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^2 + b^2 = c^k := by
  use 3 * 5 ^ (k - 1)
  use 4 * 5 ^ (k - 1)
  use 25
  have h1 : 3 * 5 ^ (k - 1) > 0 := by
    apply Nat.mul_pos
    · norm_num
    · positivity
  have h2 : 4 * 5 ^ (k - 1) > 0 := by
    apply Nat.mul_pos
    · norm_num
    · positivity
  have h3 : (25 : ℕ) > 0 := by norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · -- Now need to prove that (3 * 5 ^ (k - 1)) ^ 2 + (4 * 5 ^ (k - 1)) ^ 2 = (25 : ℕ) ^ k
    have h4 : (3 * 5 ^ (k - 1)) ^ 2 + (4 * 5 ^ (k - 1)) ^ 2 = (25 : ℕ) ^ k := by
      induction k with
      | zero =>
        exfalso
        exact Nat.lt_irrefl 0 hk
      | succ k ih =>
        cases k with
        | zero =>
          all_goals norm_num
        | succ k =>
          simp [pow_succ, pow_two, Nat.mul_comm] at ih ⊢
          <;> nlinarith [ih]
          all_goals norm_num
    linarith [h4]