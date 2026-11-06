import Mathlib

/-To celebrate the $20$th LMT, the LHSMath Team bakes a cake. Each of the $n$ bakers places $20$ candles on the cake. When they count, they realize that there are $(n -1)!$ total candles on the cake. Find $n$.
-/
theorem algebra_35179 {n : ℕ} (hn : n > 0) (h : 20 * n = Nat.factorial (n - 1)) :
    n = 6 := by
  -- We start with the equation given in the problem: $20n = (n-1)!$ We need to find the value of $\( n \)$ that satisfies this equation.
  have h1 : n ≤ 6 := by
    by_cases h2 : n ≤ 6
    · exact h2
    · -- To ensure there are no solutions that satisfy $n>6$, we note that for ( n &gt; 6 ), the factorial function ((n-1)!) grows much faster than the linear function (20n). 
      have h3 : n ≥ 7 := by omega
      have h4 : 20 * n < Nat.factorial (n - 1) := by
        have h5 : n ≥ 7 := h3
        have h6 : n - 1 ≥ 6 := by
          omega
        have h7 : Nat.factorial (n - 1) > 20 * n := by
          have h8 : n ≥ 7 := h5
          have h9 : n - 1 ≥ 6 := by omega
          have h10 : ∀ m, m ≥ 6 → Nat.factorial m > 20 * (m + 1) := by
            intro m hm
            -- we have $\(n-1\)!>20*n$ when $n=7$
            have base := show Nat.factorial 6 > 20 * (6 + 1) by
              norm_num [Nat.factorial]
            -- and we can prove the inequality holds for any $m>6$ by induction
            have step : ∀ k, k ≥ 6 → (Nat.factorial k > 20 * (k + 1)) → Nat.factorial (k + 1) > 20 * ((k + 1) + 1) := by
              intros k hk hfactorial
              have h1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
                rw [Nat.factorial_succ]
              rw [h1]
              have h2 : (k + 1) * Nat.factorial k > (k + 1) * (20 * (k + 1)) := by
                nlinarith [hfactorial]
              have h3 : (k + 1) * (20 * (k + 1)) ≥ 20 * ((k + 1) + 1) := by
                nlinarith [hk]
              linarith
            exact Nat.le_induction base step m hm
          have h11 : Nat.factorial (n - 1) > 20 * n := by
            have h12 : n - 1 ≥ 6 := by omega
            specialize h10 (n - 1) h12
            have h13 : 20 * n = 20 * ((n - 1) + 1) := by omega
            linarith
          linarith
        linarith
      linarith
  -- we can easily solve the equation now by cases $n=1,2,...6$.
  have h2 : n ≤ 6 := h1
  interval_cases n <;> simp [Nat.factorial] at h ;omega