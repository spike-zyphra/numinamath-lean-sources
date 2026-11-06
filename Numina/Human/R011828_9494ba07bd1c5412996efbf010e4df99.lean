import Mathlib
/- Let $m$ and $n$ be positive integers such that $m - n = 189$ and such that the least common multiple of $m$ and $n$ is equal to $133866$. Find $m$ and $n$. -/
theorem number_theory_60858 {m n : ℕ} (hm : m > 0) (hn : n > 0) (hmn : m - n = 189) (hlcm : Nat.lcm m n = 133866) :
m = 1998 ∧ n = 1809:= by
  -- Rewrite the constraint m - n = 189 as m = n + 189
  replace hmn : m = n + 189:= by omega
  -- Define d as the greatest common divisor of m and n
  set d:= Nat.gcd m n with hd
  clear_value d
  -- Show that d is positive since m is positive
  have hdpos : d > 0:= by
    subst d
    exact Nat.gcd_pos_of_pos_left n hm
  -- d divides m
  have h1 : d ∣ m:= by subst d ; exact Nat.gcd_dvd_left m n
  -- d divides n
  have h2 : d ∣ n:= by subst d ; exact Nat.gcd_dvd_right m n
  -- Express m and n in terms of d and their quotients
  rcases h1 with ⟨m1, hm1⟩
  rcases h2 with ⟨n1, hn1⟩
  subst m n
  -- Show that d divides 189
  have h3 : d ∣ 189:= by
    have g1 : d ∣ d * n1:= by simp
    suffices d ∣ d * n1 + 189 by exact (Nat.dvd_add_iff_right g1).mpr this
    rw [hm1]
    simp
  -- Substitute the expressions for m and n into the lcm equation
  rw [hm1] at hlcm hd
  -- Use the property that lcm(d*a, d*b) = d * lcm(a, b)
  rw [show Nat.lcm (d * m1) (d * n1) = d * Nat.lcm m1 n1 by rw [Nat.lcm_mul_left]] at hlcm
  -- Use the property that gcd(d*a, d*b) = d * gcd(a, b)
  rw [show Nat.gcd (d * m1) (d * n1) = d * Nat.gcd m1 n1 by rw [Nat.gcd_mul_left]] at hd
  -- Show that m1 and n1 are coprime (gcd = 1)
  replace hd : Nat.gcd m1 n1 = 1:= by exact (Nat.mul_right_eq_self_iff hdpos).mp (id (Eq.symm hd))
  -- For coprime numbers, lcm(a, b) = a * b
  rw [show Nat.lcm m1 n1 = m1 * n1 by exact Nat.Coprime.lcm_eq_mul hd] at hlcm
  -- d must be a divisor of 189
  replace h3 : d ∈ Nat.divisors 189:= by refine Nat.mem_divisors.mpr ⟨h3, by omega⟩
  -- Compute all divisors of 189
  have h4 : Nat.divisors 189 = {1, 3, 7, 9, 21, 27, 63, 189}:= by native_decide
  rw [h4] at h3
  -- Case analysis on each possible value of d
  fin_cases h3
  .
    -- Case d = 1: leads to a contradiction (571185 is not a perfect square)
    replace hlcm : IsSquare 571185:= by
      simp at hm1
      subst m1
      rw [show 571185 = (2 * n1 + 189) ^ 2 by linarith]
      use (2 * n1 + 189)
      ring
    absurd hlcm
    native_decide
  .
    -- Case d = 3: leads to a contradiction (182457 is not a perfect square)
    replace hm1 : m1 = n1 + 63:= by omega
    subst m1
    replace hlcm : IsSquare 182457:= by
      rw [show 182457 = (2 * n1 + 63) ^ 2 by linarith]
      use (2 * n1 + 63)
      ring
    absurd hlcm
    native_decide
  .
    -- Case d = 7: impossible by omega
    omega
  .
    -- Case d = 9: leads to a contradiction (59937 is not a perfect square)
    replace hm1 : m1 = n1 + 21:= by omega
    subst m1
    replace hlcm : IsSquare 59937:= by
      rw [show 59937 = (2 * n1 + 21) ^ 2 by linarith]
      use (2 * n1 + 21)
      ring
    absurd hlcm
    native_decide
  .
    -- Case d = 21: impossible by omega
    omega
  .
    -- Case d = 27: this is the valid case that gives us the solution
    replace hm1 : m1 = n1 + 7:= by omega
    subst m1
    -- Show that (2*n1 + 7)² = 141²
    replace hlcm : (2 * n1 + 7) ^ 2 = 141 ^ 2:= by linarith
    -- Therefore 2*n1 + 7 = 141
    replace hlcm : 2 * n1 + 7 = 141:= by nlinarith only [hlcm]
    -- This gives us the final answer
    refine ⟨by linarith, by linarith⟩
  -- All remaining cases are impossible by omega
  all_goals
    omega
