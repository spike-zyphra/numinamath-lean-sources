import Mathlib

open Nat

/- $5 \cdot 15$ Assume $d$ is the greatest common divisor of the positive integers $a$ and $b$, and $d^{\prime}$ is the greatest common divisor of the positive integers $a^{\prime}$ and $b^{\prime}$. Prove that the greatest common divisor of the numbers $a a^{\prime}, a b^{\prime}, b a^{\prime}, b b^{\prime}$ is equal to $d d^{\prime}$.
(Hungarian Mathematical Olympiad, 1913) -/
theorem number_theory_136392 {a b a' b' d d' : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ha' : 0 < a') (hb' : 0 < b') (hd : d = Nat.gcd a b) (hd' : d' = Nat.gcd a' b')
    (h : a = a' * d) (h' : b = b' * d') :
    Nat.gcd (a * a') (Nat.gcd (a * b') (Nat.gcd (b * a') (b * b'))) = d * d' := by
  trans Nat.gcd (Nat.gcd (a * a') (a * b')) (Nat.gcd (b * a') (b * b'))
  · -- Apply associativity of gcd
    rw [Nat.gcd_assoc]
  -- Now factor out common factors in the gcd
  rw [gcd_mul_left, gcd_mul_left, gcd_mul_right]
  -- We now just rewrite in terms of the given definitions
  rw [hd, hd']