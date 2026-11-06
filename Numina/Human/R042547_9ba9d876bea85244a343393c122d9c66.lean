import Mathlib

/- (i) \( \binom{n}{0} = \binom{n}{n} = 1 \) -/
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

/- (ii) \( \binom{n}{k} = \binom{n}{n-k} \). -/
theorem number_theory_4463_2 {n k : ℕ} (hkn : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  have hnk : n - k ≤ n := by simp
  have hnnk : n - (n - k) = k := Nat.sub_sub_self hkn
--    \[
-- \binom{n}{k} = \frac{n!}{k! \cdot (n-k)!}.
-- \]
-- Now, we can rewrite \( (n-k)! \) as \( (n - (n-k))! \), which gives us:
-- \[
-- \binom{n}{k} = \frac{n!}{k! \cdot (n-k)!} = \frac{n!}{(n-k)! \cdot (n - (n-k))!} = \binom{n}{n-k}.
-- \]
  rw [Nat.choose_eq_factorial_div_factorial hkn, Nat.choose_eq_factorial_div_factorial hnk, hnnk, mul_comm]
