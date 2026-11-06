import Mathlib


/- Let the term $S_n$ be the sum of the first $n$ powers of $2$. For instance, $S_19108 = 2^0 + 2^1 + 2^2 = 7$.  Find the largest possible value of the greatest common divisor of two consecutive terms, $S_n$ and $S_{n+1}$, for any $n$. -/
theorem number_theory_19108 (S : ℕ → ℕ) (hS : S = fun n => ∑ i in Finset.range n, 2 ^ i):
    IsGreatest {x | ∃ n, x = Nat.gcd (S n) (S (n + 1))} 1 := by
        -- 分两步证明：能取等 + 最大值
        constructor <;>
        simp [upperBounds]
        -- 能取等
        .
            use 1
            simp [hS]
        -- 最大值
        .
            -- 证明 S n = 2 ^ n - 1
            have h : ∀ n : ℕ, S n = 2 ^ n - 1:= by
              intro n
              induction n with
              | zero =>
                simp [hS]
              | succ n ih =>
                simp [hS] at ih
                simp [hS]
                rw [Finset.range_succ]
                simp
                rw [ih]
                have g : 2 ^ n ≥ 1:= by exact Nat.one_le_two_pow
                have g1 : 2 ^ n + (2 ^ n - 1) = 2 ^ n + 2 ^ n - 1:= Eq.symm (Nat.add_sub_assoc g (2 ^ n))
                rw [g1]
                rw [show 2 ^ n + 2 ^ n = 2 ^ (n + 1) by ring]
            intro n
            have h1 := h n
            have h2 := h (n + 1)
            have h3 : S n ≤ S (n + 1):= by
                rw [h1, h2]
                omega
            -- 证明 Nat.gcd (S n) (S (n + 1)) = Nat.gcd (S n) (S (n + 1) - S n)
            have h4 : Nat.gcd (S n) (S (n + 1)) = Nat.gcd (S n) (S (n + 1) - S n):= Eq.symm (Nat.gcd_sub_self_right h3)
            rw [h4, h1, h2]
            -- 化简表达式
            have h5 : 2 ^ (n + 1) - 1 - (2 ^ n - 1) = 2 ^ n:= by
                ring_nf
                have g1 : 2 ^ n ≥ 1:= by exact Nat.one_le_two_pow
                have g2 : 2 ^ n * 2 - 1 ≥ 2 ^ n - 1:= by omega
                have g3 : 2 ^ n * 2 - 1 - (2 ^ n - 1) + (2 ^ n - 1) = 2 ^ n + (2 ^ n - 1):= by
                    rw [show 2 ^ n * 2 - 1 - (2 ^ n - 1) + (2 ^ n - 1) = 2 ^ n * 2 - 1 by exact Nat.sub_add_cancel g2]
                    rw [show 2 ^ n + (2 ^ n - 1) = 2 ^ n + 2 ^ n - 1 by exact Eq.symm (Nat.add_sub_assoc g1 (2 ^ n))]
                    ring_nf
                exact Eq.symm (Nat.add_right_cancel (id (Eq.symm g3)))
            rw [h5]
            -- 利用 Nat.gcd (2 ^ n - 1) (2 ^ n) = Nat.gcd (2 ^ n - 1) (2 ^ n - (2 ^ n - 1))
            rw [show Nat.gcd (2 ^ n - 1) (2 ^ n) = Nat.gcd (2 ^ n - 1) (2 ^ n - (2 ^ n - 1)) by refine Eq.symm (Nat.gcd_sub_self_right (by omega))]
            rw [show 2 ^ n - (2 ^ n - 1) = 1 by refine Nat.sub_sub_self (by exact Nat.one_le_two_pow)]
            rw [show Nat.gcd (2 ^ n - 1) 1 = 1 by exact Nat.gcd_one_right (2 ^ n - 1)]
