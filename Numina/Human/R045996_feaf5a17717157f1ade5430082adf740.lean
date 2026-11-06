import Mathlib

open Nat

/- Let $ n $ and $ k $ be positive integers with $ n \geq k $. Then the following identity holds:
$$
\binom{n}{k} + \binom{n}{k-1} = \binom{n+1}{k}
$$ -/
theorem number_theory_4572'
    (n k : ℕ) (hpos : k > 0) (hle : k ≤ n) :
    Nat.choose n k + Nat.choose n (k - 1) = Nat.choose (n + 1) k := by
  -- $\binom{n}{k} * k! * (n+1-k)! = n! * (n+1-k) $
  have hmul1 : n.choose k * (k ! * (n + 1 - k)!) = ((n !) * (n + 1 - k)) := by
    have := choose_mul_factorial_mul_factorial (show k ≤ n by omega)
    rw [Nat.sub_add_comm hle,
        ← mul_assoc, factorial_succ (n - k), mul_comm (n - k + 1), ← mul_assoc]
    congr
  -- $\binom{n}{k-1} * k! * (n+1-k)! = n! * k $
  have hmul2 : n.choose (k - 1) * (k ! * (n + 1 - k)!) = (n ! * k) := by
    have := choose_mul_factorial_mul_factorial (show (k - 1) ≤ n by omega)
    rw [← mul_assoc, ← mul_factorial_pred hpos, mul_comm k (k - 1)!,
        mul_assoc, mul_assoc, mul_comm k, ← mul_assoc, ← mul_assoc,
        show n + 1 - k = n - (k - 1) by omega]
    congr
  -- need to perform division
  have hpos : (k ! * (n + 1 - k)!) ≠ 0 := by
    apply mul_ne_zero <;> simp [factorial_ne_zero]
  -- combine hmul1 and hmul2, we get
  -- $(\binom{n}{k} + \binom{n}{k-1}) * k! * (n+1-k)! = (n+1)!$
  have : (n.choose k + n.choose (k - 1)) * (k ! * (n + 1 - k)!) = (n + 1)! := by
    rw [add_mul, hmul1, hmul2, ← mul_add,
        show n + 1 - k + k = n + 1 by omega,
        mul_comm, factorial_succ]
  -- definition of factorial
  conv => rhs; rw [choose_eq_factorial_div_factorial (by omega)]
  -- perform division
  exact Nat.eq_div_of_mul_eq_left hpos this
