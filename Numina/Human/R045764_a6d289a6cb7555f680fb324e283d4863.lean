import Mathlib

/- As $n$ ranges over the positive integers, what is the maximum possible value for the greatest common divisor of $11n+3$ and $6n+1$? -/
theorem number_theory_11389 :
    IsGreatest {x | ∃ n : ℕ, 0 < n ∧ x = Nat.gcd (11 * n + 3) (6 * n + 1)} 7 := by
  -- use the Euclidean Algorithm to simplify
  have h1: ∀n:ℕ, 0 < n → (11*n+3).gcd (6*n+1) = (n-1).gcd 7 := by
    intro n hn
    -- integer > 0 is equivalent to ≥ 1
    change n ≥ 1 at hn
    rw [← Nat.gcd_sub_self_left (by linarith)]; simp
    have ht1: 11*n+2-6*n = 5*n + 2 := by omega
    -- when n ≥ 1, 5n+2 ≤ 6n+1
    have ht2: 5*n + 2 ≤ 6*n + 1 := by omega
    rw [ht1, ← Nat.gcd_sub_self_right ht2]; simp
    have ht3: 6*n - (5*n+1) = n-1 := by omega
    rw [ht3]
    -- (5n+2).gcd n-1 = ((5n+2)-5(n-1)).gcd (n-1), we sub 5 times, 5n+2-5(n-1) = 7 still ≥ 0.
    rw [← Nat.gcd_sub_self_left (by omega)]
    rw [← Nat.gcd_sub_self_left (by omega)]
    rw [← Nat.gcd_sub_self_left (by omega)]
    rw [← Nat.gcd_sub_self_left (by omega)]
    rw [← Nat.gcd_sub_self_left (by omega)]
    -- now left side is 7.
    have ht4: (5*n + 2 - (n-1) - (n-1) - (n-1) - (n-1) - (n-1)) = 7 := by omega
    rw [ht4]
    apply Nat.gcd_comm
  -- begin solving the problem
  rw [IsGreatest, upperBounds]; simp
  constructor
  --verify 7 satisfies the condition
  · use 1; simp
  -- show gcd ≤ 7
  · intro a n hn aeq
    rw [h1 n hn] at aeq
    rw [aeq]
    apply Nat.gcd_le_right 
    norm_num