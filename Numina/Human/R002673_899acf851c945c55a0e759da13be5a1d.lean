import Mathlib

/--  Let P(x) be a polynomial with integer coefficients that satisfies
    P(17)=10 and P(24)=17. Given that P(n)=n+3
    has two distinct integer solutions n1​ and n2, find the product n1 * n2. -/
theorem algebra_98610 {P : Polynomial ℤ} (hP1 : P.eval 17 = 10) (hP2 : P.eval 24 = 17)
    (n1 n2 : ℤ) (hn1 : P.eval n1 = n1 + 3) (hn2 : P.eval n2 = n2 + 3)
    (hne : n1 ≠ n2) : n1 * n2 = 418 := by
  -- We have P(n_1) = n_1 + 3, P(n_2) = n_2 + 3.
  -- Using the property that a - b | P(a) - P(b) whenever a and b are distinct integers,
  -- we get n1 - 17 | P(n1) - P(17) = n1 + 3 - 10 = n1 - 7.
  have n17 {n} (hn : P.eval n = n + 3) : n - 17 ∣ n - 7 := by
    apply (P.sub_dvd_eval_sub n 17).trans
    rw[hP1, hn]
    apply of_eq
    omega
  -- and n1 - 23 | P(n1) - P(24) = n1 + 3 - 17 = n1 - 14.
  have n14 {n} (hn : P.eval n = n + 3) : n - 24 ∣ n - 14 := by
    apply (P.sub_dvd_eval_sub n 24).trans
    rw[hP2, hn]
    apply of_eq
    omega
  -- Since n1 - 7 = 10 + (n1 - 17) and n1 - 14 = 10 + (n1 - 24),
  -- we must have n1 - 17 | 10
  have n1710 {n} (hn : P.eval n = n + 3): n - 17 ∣ 10 := by
    convert dvd_sub (n17 hn) dvd_rfl
    ring
  -- and n1 - 24 | 10.
  have n2410 {n} (hn : P.eval n = n + 3) : n - 24 ∣ 10 := by
    convert dvd_sub (n14 hn) dvd_rfl
    ring
  have divisors : (10 : ℕ).divisors = {1,2,5,10} := rfl
  -- We compute the divisors of 10 to {-10,-5,-2,-1,1,2,5,10}.
  have div_10_iff (x : ℤ) : x ∣ 10 ↔ x ∈ ({-10,-5,-2,-1,1,2,5,10} : Finset ℤ) := by
    change x ∣ (↑ (10 : ℕ)) ↔ x ∈ ({-10,-5,-2,-1,1,2,5,10} : Finset ℤ)
    rw[Int.dvd_natCast, ← and_iff_left (a := x.natAbs ∣ 10) (b := 10 ≠ 0) (by simp),
       ← Nat.mem_divisors, divisors]
    simp only [Finset.mem_insert, Finset.mem_singleton, Int.reduceNeg]
    omega
  -- We look for two divisors of 10 that differ by 7, and find that the lower divisors must be -5 or -2.
  have {n} (hn : P.eval n = n + 3) : n - 24 ∈ ({-5,-2} : Finset ℤ) := by
    have n24 := (div_10_iff _).mp $ n2410 hn
    have n17 := (div_10_iff _).mp $ n1710 hn
    convert_to (n - 24) + 7 ∈ ({-10, -5, -2, -1, 1, 2, 5, 10} : Finset ℤ) at n17
    · ring
    · generalize n - 24 = n at *
      fin_cases n24 <;> [simp at n17; simp; simp; simp at n17; simp at n17; simp at n17; simp at n17; simp at n17]
  -- Note that all of these computations apply to both n1 and n2, hence n1 - 24 = -5, n2 - 24 = -2
  -- or the other way around.
  replace hn1 := this hn1
  replace hn2 := this hn2
  simp at hn1 hn2
  -- Either way, n1 * n2 = 19 * 22 = 418.
  rcases hn1 with (hn1|hn1)
  · rcases hn2 with (hn2|hn2)
    · omega
    · obtain rfl : n1 = 19 := by linarith
      obtain rfl : n2 = 22 := by linarith
      rfl
  · rcases hn2 with (hn2|hn2)
    · obtain rfl : n2 = 19 := by linarith
      obtain rfl : n1 = 22 := by linarith
      rfl
    · omega