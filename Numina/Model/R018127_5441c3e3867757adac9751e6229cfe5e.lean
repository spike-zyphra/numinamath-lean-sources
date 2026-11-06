import Mathlib

theorem number_theory_250163 (n : ℕ) (hn : n > 0) :
    ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ n = (a^2 - b^2) / (c^2 + d^2) := by
  use 1 + 2 * n
  use 2 * n - 1
  use 2
  use 2
  have ha : 1 + 2 * n > 0 := by omega
  have hb : 2 * n - 1 > 0 := by
    omega
  have hc : 2 > 0 := by norm_num
  have hd : 2 > 0 := by norm_num
  have heq : n = ((1 + 2 * n) ^ 2 - (2 * n - 1) ^ 2) / ((2 : ℕ) ^ 2 + (2 : ℕ) ^ 2) := by
    have eq1 : ((1 + 2 * n) : ℕ) ^ 2 - ((2 * n - 1) : ℕ) ^ 2 = 8 * n := by 
      cases n with
      | zero => omega
      | succ n =>
        simp [Nat.pow_add, Nat.pow_mul, mul_add, add_mul, pow_two]
        <;> ring_nf
        <;> omega
    have eq2 : ((2 : ℕ) : ℕ) ^ 2 + (2 : ℕ) ^ 2 = 8 := by
      norm_num
    calc
      n = 8 * n / 8 := by
        omega
      _ = ( ((1 + 2 * n) ^ 2 - (2 * n - 1) ^ 2) ) / ( ((2 : ℕ) ^ 2 + (2 : ℕ) ^ 2) ) := by
        rw [eq1, eq2]
        all_goals norm_num
        <;> ring_nf
        <;> omega
  constructor
  · exact ha
  constructor
  · exact hb
  constructor
  · exact hc
  constructor
  · exact hd
  · exact heq