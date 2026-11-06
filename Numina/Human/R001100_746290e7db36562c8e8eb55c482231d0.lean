import Mathlib

/- Amy, Ben, Carl, and Debbie each have some coins. Ben has three times the number of coins that Amy has and a third of the number of coins that Carl has, and Debbie has two-thirds the number of coins that Carl has. The number of coins that Amy has, multiplied by the number of coins that Ben has, multiplied by the number of coins that Carl has, multiplied by the number of coins that Debbie has, is $162$. How many coins do the four children have all together? -/
theorem algebra_20460 {a b c d : ℕ}
    (h₀ : (b : ℝ) = 3 * a)
    (h₁ : (b : ℝ) = c / 3)
    (h₂ : (d : ℝ) = 2 * c / 3)
    (h₃ : a * b * c * d = 162) :
    a + b + c + d = 19 := by
  -- $b = 3a$
  have beq : b = 3 * a := by
    have beq : (b : ℝ) = (3 * a : ℕ) := by
      rw [h₀]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact Nat.cast_injective beq
  -- $c = 9a$
  have ceq : c = 9 * a := by
    have ceq : (c : ℝ) = (9 * a : ℕ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    exact Nat.cast_injective ceq
  -- $d = 6a$
  have deq : d = 6 * a := by
    have deq : (d : ℝ) = (6 * a : ℕ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    exact Nat.cast_injective deq
  -- $162a = a$, so $a = 1$
  rw [beq, ceq, deq] at h₃
  ring_nf at h₃
  have aeq : a ^ 4 = 1 ^ 4 := by
    linarith
  apply Nat.pow_left_injective at aeq
  -- So $a + b + c + d = 162$
  linarith
  exact Ne.symm (Nat.zero_ne_add_one 3)