import Mathlib

/- 2. Find the numbers $a$ and $n$ knowing that $a$ is a prime number, $n \in \mathbb{N}^{*}$, and $a^{2 n}-5=4\left(5+5^{2}+\cdots+5^{2015}\right)$.

Prof.Vlad Emil, Zimnicea -/
theorem number_theory_120202 (a n : ℕ) (ha : Nat.Prime a)
    (h : a^(2 * n) - 5 = 4 * ∑ i ∈ Finset.range 2015, 5^(i + 1)) :
    a = 5 ∧ n = 1008 := by
  -- Show that 4 * ∑ i ∈ Finset.range k, 5^(i + 1) = 5 ^ (k + 1) - 5 for all k.
  -- The result follows from the formula for the sum of a geometric progression.
  have eq k : 4 * ∑ i ∈ Finset.range k, 5^(i + 1) = 5 ^ (k + 1) - 5 := calc
    4 * ∑ i ∈ Finset.range k, 5^(i + 1) = ((∑ i ∈ Finset.range k, (4 + 1)^i) * 4 + 1) * 5 - 5 := by
      simp [pow_succ, add_mul, ← Finset.sum_mul]
      ring
    _ = (4 + 1)^k * 5 - 5 := by rw [geom_sum_mul_add]
    _ = 5^(k + 1) - 5 := by rw [← pow_succ]
  -- We get a^(2 * n) = 5^2016.
  replace eq : a ^ (2 * n) = 5 ^ 2016 := by
    rw [eq] at h
    omega
  -- Show that a = 5.
  have a_eq : a = 5 := by
    symm
    -- It is enough to show that 5 ∣ a (because 5 and a are prime numbers).
    rw [← Nat.prime_dvd_prime_iff_eq Nat.prime_five ha]
    -- It is enough to show that 5 divides a ^ (2 * n) = 5 ^ 2016.
    apply Nat.prime_five.dvd_of_dvd_pow (n := 2 * n)
    rw [eq]
    apply dvd_pow_self _ (by norm_num)
  subst a
  -- a = 5 and we have 5 ^ (2 * n) = 5 ^ 2016, so 2 * n = 2016, n = 1008.
  have := Nat.pow_right_injective (show 2 ≤ 5 by norm_num) eq
  omega