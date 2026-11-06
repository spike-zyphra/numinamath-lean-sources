import Mathlib

-- Use three step induction, inspired by Nat.twoStepInduction
def l_threeStepInduction {P : ℕ → Sort*} (zero : P 0) (one : P 1) (two : P 2)
    (more : ∀ n, P n → P (n + 1) → P (n + 2) → P (n + 3)) : ∀ a, P a
  | 0 => zero
  | 1 => one
  | 2 => two
  | _ + 3 => more _ (l_threeStepInduction zero one two more _) (l_threeStepInduction zero one two more _) (l_threeStepInduction zero one two more _)

/- 6. Given the sequence $\left\{a_{n}\right\}$ satisfies $a_{1}=1, a_{2}=4, a_{3}=10$, for any $n \geqslant 2$ there is $a_{n+1}^{2}-2 a_{n}^{2}=$ $a_{n} a_{n+2}-2 a_{n-1} a_{n+1}$, then the unit digit of $a_{21}$ is $\qquad$. -/
theorem algebra_110286 {a : ℕ → ℤ} (ha1 : a 0 = 1) (ha2 : a 1 = 4) (ha3 : a 2 = 10)
    (han : ∀ n ≥ 1, (a (n + 1)) ^ 2 - 2 * (a n) ^ 2 = a n * a (n + 2) - 2 * a (n - 1) * a (n + 1)) :
    a 20 % 10 = 6 := by
  -- Claim an explicit formula for a n
  have formula : ∀ n, a n = 3 * 2 ^ n - 2 := by
    intro n
    -- Use the induction scheme
    induction n using l_threeStepInduction with
    | zero => aesop
    | one => aesop
    | two => aesop
    | more k ih₀ ih₁ ih₂ =>
      specialize han (k + 1)
      -- Simplify han
      conv at han =>
        simp
        rw [show k + 1 + 1 = k + 2 by linarith, show k + 1 + 2 = k + 3 by linarith, ih₀, ih₁, ih₂]
        simp [sub_sq, sub_sq, mul_sub, mul_pow, ← pow_mul, sub_mul, ← sub_add, mul_add]
        rw [← sub_mul, eq_sub_iff_add_eq]
        lhs
        ring
        equals (3 * 2 ^ (k + 1) - 2) * (3 * 2 ^ (k + 3) - 2) => ring
      -- Cancel the left factor
      rw [mul_right_inj' (by omega)] at han
      · tauto
  -- Use the formula
  rw [formula]
  -- Use arithmetic
  norm_num