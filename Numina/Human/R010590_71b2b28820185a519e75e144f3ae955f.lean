import Mathlib

open Nat Real Finset

/-- The sum of the base-$10$ logarithms of the divisors of $10^n$ is $792$. What is $n$?
$\text{(A)}\ 11\qquad \text{(B)}\ 12\qquad \text{(C)}\ 13\qquad \text{(D)}\
14\qquad \text{(E)}\ 15$ -/
theorem number_theory_1197 (n : ℕ) (h : ∑ d ∈ divisors (10^n), logb 10 d = 792) : n = 11 := by

  -- Prime factorization of $10^n$ is $2^n \cdot 5^n$.
  have h10pow : 10^n = 2^n * 5^n := by rw [←mul_pow]; norm_num

  -- Therefore, every factor of $10^n$ will be of the form $2^a \times 5^b , a\leq n , b\leq n$.
  have : divisors (10^n) =
      Finset.image (fun p => 2^(p.1) * 5^(p.2))
      ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))) := by
    ext d
    simp [h10pow, divisors_mul, Finset.mem_mul, divisors_prime_pow (p := 2) (by decide),
          divisors_prime_pow (p := 5) (by decide)]
    tauto

  -- So, we can rewrite the sum as $\sum_{a=0}^{n} \, \sum_{b=0}^{n} \, \log(2^a 2^b).$
  have : ∑ d ∈ divisors (10^n), logb 10 d =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), logb 10 (2^a * 5^b) := by
    rw [this, Finset.sum_image, Finset.sum_product]
    · push_cast
      rfl
    · simp
      intro a b ha hb a' b' ha' hb' h

      -- The number of $2$'s in the prime factorization of $2^a * 5^b$ is $a$.
      have hfac2 (a b : ℕ) : a = (2^a * 5^b).factorization 2 := by
        calc a = a*1 := by simp
            _ = a*((2).factorization 2) := by congr 1; native_decide
            _ = ((2^a).factorization 2) := by simp [factorization_pow]
            _ = ((2^a).factorization 2) + b*0 := by simp
            _ = ((2^a).factorization 2) + b*((5).factorization 2) := by congr 2; native_decide
            _ = ((2^a).factorization 2) + ((5^b).factorization 2) := by simp [factorization_pow]
            _ = _ := by simp [factorization_mul]

      -- The number of $5$'s in the prime factorization of $2^a * 5^b$ is $b$.
      have hfac5 (a b : ℕ) : b = (2^a * 5^b).factorization 5 := by
        calc b = b*1 := by simp
            _ = b*((5).factorization 5) := by congr 1; native_decide
            _ = ((5^b).factorization 5) := by simp [factorization_pow]
            _ = a*0 + ((5^b).factorization 5) := by simp
            _ = a*((2).factorization 5) + ((5^b).factorization 5) := by congr 2; native_decide
            _ = ((2^a).factorization 5) + ((5^b).factorization 5) := by simp [factorization_pow]
            _ = _ := by simp [factorization_mul]

      rw [hfac2 a b, hfac2 a' b', h, hfac5 a b, hfac5 a' b', h]
      trivial

  have hgauss : ∑ i ∈ Finset.range (n + 1), (i : ℝ) = (n : ℝ) * (n + 1) / 2 := by
      rw [←cast_sum, Finset.sum_range_id, mul_comm]
      simp
      norm_cast
      rw [Nat.cast_div ?_ (by norm_num)]
      · congr
      · rcases (even_or_odd' n) with ⟨k, rfl | rfl⟩
        · use k * (2*k + 1)
          ring
        · use (k + 1) * (2*k + 1)
          ring

  -- Simplify the summation using the logarithmic identity $\log(a \cdot b) = \log(a) + \log(b)$
  -- and the Gauss formula $0 + 1 + \dots + n = n (n + 1) / 2$.
  simp [this, logb_mul, logb_pow, Finset.sum_add_distrib, Finset.sum_const, ←Finset.sum_mul,
        hgauss, ←Finset.mul_sum] at h

  have : logb 10 2 = 1 - logb 10 5 := by
    calc _ = logb 10 2 + logb 10 5 - logb 10 5 := by ring
         _ = 1 - logb 10 5 := by rw [←logb_mul (by norm_num) (by norm_num)]; norm_num
  rw [this] at h

  -- Logarithms cancels out. After simplifying, we get $n(n+1)^2 = 1584$.
  replace h : (n : ℝ) * (n + 1)^2 = 1584 := by
    linarith
  norm_cast at h

  -- From this equation, we can immediately deduce that $n = 11$.
  nlinarith