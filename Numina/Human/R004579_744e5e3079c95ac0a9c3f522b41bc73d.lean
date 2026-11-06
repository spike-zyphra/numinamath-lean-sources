import Mathlib

open Nat

/- (14) (10 points) Given the sequence $\left\{a_{n}\right\}$ satisfies: $a_{1}=1,2^{n} \cdot\left(a_{n+1}-a_{n}\right)=a_{n}$, prove that when $n \geqslant 3$, $2-\frac{1}{2^{n-1}}<a_{n}<\left(\frac{3}{2}\right)^{n-1}$. -/
theorem algebra_286261 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han : ∀ n, 2 ^ n * (a (n + 1) - a n) = a n)
    (n : ℕ) (hn : 3 ≤ n) :
    2 - 1 / 2 ^ (n - 1) < a n ∧ a n < (3 / 2) ^ (n - 1) := by
  -- General formula for a (n + 1)
  have a_formula : ∀ n, a (n + 1) = a n * (1 + 1 / 2 ^ n) := by
    intro n
    specialize han n
    rw [mul_add, mul_one, ← @mul_right_inj' _ _ (2 ^ n) (a (n + 1)) _ (show 2 ^ n ≠ 0 by exact pow_ne_zero n (by norm_num)), mul_add]
    conv_rhs =>
      rhs
      rw [mul_comm (a n), ← mul_assoc]
      simp
    linarith
  -- Use induction on n
  induction n, hn using le_induction with
  | base => -- Verify the case n = 3
    -- Find the value of a 2
    have ha2 : _ := a_formula 1
    rw [ha1] at ha2
    norm_num at ha2
    -- Find the value of a 3
    have ha3 : _ := a_formula 2
    rw [ha2] at ha3
    norm_num at ha3
    rw [ha3]
    norm_num
  -- Induction step
  | succ k hk ih =>
    rw [a_formula k]
    constructor
    · -- Prove the lower bound
      rw [← gt_iff_lt]
      calc
        -- It's enough to directly use the induction hypothesis
        a k * (1 + 1 / 2 ^ k) > (2 - 1 / 2 ^ (k - 1)) * (1 + 1 / 2 ^ k) := by rw [gt_iff_lt, mul_lt_mul_right (by positivity)]; tauto
        _ = 2 - 1 / 2 ^ (2 * k - 1) := by
          -- Lot of simplification
          rw [sub_mul, mul_add, mul_add]
          simp only [← zpow_natCast, one_div, ← inv_pow, ← zpow_neg_one, mul_one, ← zpow_mul, mul_neg]
          nth_rw 2 [← zpow_one 2]
          rw [← zpow_add₀ (by positivity), ← zpow_add₀ (by positivity)]
          rw [Int.natCast_sub (show 1 ≤ k by linarith), neg_sub, ← sub_eq_add_neg, ← sub_eq_add_neg, Int.natCast_sub (show 1 ≤ 2 * k by linarith)]
          rw [sub_sub, ← two_mul, ← sub_sub]
          simp
        _ > _ := by
          simp
          rw [inv_lt_inv₀ (by positivity) (by positivity)]
          refine pow_lt_pow_right₀ (by linarith) ?_
          -- Show that 2 * k - 1 > k
          apply lt_sub_of_add_lt
          linarith
    -- Prove the upper bound
    calc
      -- It's enough to directly use the induction hypothesis
      a k * (1 + 1 / 2 ^ k) < (3 / 2) ^ (k - 1) * (1 + 1 / 2 ^ k) := by rw [mul_lt_mul_right (by positivity)]; tauto
      _ < (3 / 2) ^ (k - 1) * (3 / 2) := by
        rw [mul_lt_mul_left (by positivity), show (3 / 2 : ℝ) = 1 + 1 / 2 ^ 1 by norm_num]
        simp
        rw [inv_lt_inv₀ (by positivity) (by positivity)]
        nth_rw 1 [show (2 : ℝ) = 2 ^ 1 by simp]
        exact pow_lt_pow_right₀ (by linarith) (by linarith)
      _ = (3 / 2) ^ (k + 1 - 1) := by
        nth_rw 2 [show (3 / 2 : ℝ) = (3 / 2) ^ 1 by simp]
        rw [← pow_add, show k - 1 + 1 = k by exact Nat.sub_add_cancel (by linarith)]
        simp