import Mathlib

theorem number_theory_4463_1 (n : ℕ) : Nat.choose n 0 = 1 ∧ Nat.choose n n = 1 := by
  constructor
--    - For \( k = 0 \):
-- \[
-- \binom{n}{0} = \frac{n!}{0! \cdot n!} = \frac{n!}{n!} = 1.
-- \]
  . rw [Nat.choose_eq_factorial_div_factorial <| Nat.zero_le _,
      Nat.factorial_zero, one_mul, Nat.sub_zero, Nat.div_self <| Nat.factorial_pos _]
--    - For \( k = n \):
-- \[
-- \binom{n}{n} = \frac{n!}{n! \cdot 0!} = \frac{n!}{n!} = 1.
-- \]
-- Thus, both cases confirm that \( \binom{n}{0} = 1 \) and \( \binom{n}{n} = 1 \).
  rw [Nat.choose_eq_factorial_div_factorial Nat.le.refl,
    Nat.sub_self, Nat.factorial_zero, mul_one, Nat.div_self <| Nat.factorial_pos _]

theorem number_theory_4463_2 {n k : ℕ} (hkn : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  have h4 : k ≤ n := hkn
  have h11 : (n - k) ≤ n := by
    omega
  rw [Nat.choose_symm h4]
  all_goals
    all_goals omega