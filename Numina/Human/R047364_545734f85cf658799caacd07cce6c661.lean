import Mathlib

/- Let $P$ be the product of the first $100$ [positive](https://artofproblemsolving.com/wiki/index.php/Positive_integer) [odd integers](https://artofproblemsolving.com/wiki/index.php/Odd_integer). Find the largest integer $k$ such that $P$ is divisible by $3^k .$ -/
theorem number_theory_93253 :
    IsGreatest {k : ℕ | 3 ^ k ∣ ∏ i ∈ Finset.range 100, (2 * i + 1)} 49 := by
  have hfin_double : FiniteMultiplicity 3 (199).doubleFactorial := Nat.finiteMultiplicity_iff.mpr (by norm_num)
  have hfin_fact (n : ℕ) : FiniteMultiplicity 3 n.factorial := by
    rw [Nat.finiteMultiplicity_iff]
    exact ⟨by norm_num, Nat.factorial_pos n⟩
  -- it is enough to show that the multiplicity of 3 in 199!! is 49
  suffices h : multiplicity 3 (199).doubleFactorial = 49 by
    simp only [IsGreatest, Set.mem_setOf_eq, upperBounds]
    -- prove that the product of the first 100 odd positive integers is 199!!
    have eq : ∏ i ∈ Finset.range 100, (2 * i + 1) = (199).doubleFactorial := calc
      _ = ∏ i ∈ Finset.range 99, (2 * (i + 1) + 1) := by
        rw [Finset.prod_range_succ']
        simp
      _ = (199).doubleFactorial := (Nat.doubleFactorial_eq_prod_odd 99).symm
    -- the result follows from the fact that 3 ^ k ∣ x ↔ k ≤ multiplicity 3 x
    simp_rw [eq, FiniteMultiplicity.pow_dvd_iff_le_multiplicity hfin_double, h]
    trivial
  -- we have 199! = 199!! * 2 ^ 99 * 99!
  have h : (199).factorial = (199).doubleFactorial * 2 ^ 99 * (99).factorial := by
    rw [Nat.factorial_eq_mul_doubleFactorial]
    rw [show 198 = 2 * 99 by norm_num, Nat.doubleFactorial_two_mul, mul_assoc]
  -- there is a formula for computing the multiplicity of a prime number in n!
  -- use this formula to compute the multiplicity of 3 in 199!
  have h199f : multiplicity 3 (199).factorial = 97 := by
    have := @Nat.Prime.sub_one_mul_multiplicity_factorial 199 3 Nat.prime_three
    norm_num at this
    omega
  -- use the same formula to compute the multiplicity of 3 in 99!
  have h99f : multiplicity 3 (99).factorial = 48 := by
    have := @Nat.Prime.sub_one_mul_multiplicity_factorial 99 3 Nat.prime_three
    norm_num at this
    omega
  -- the multiplicity of 3 in 2 ^ 99 is 0
  have h2 : multiplicity 3 (2 ^ 99) = 0 := by
    rw [multiplicity_eq_zero]
    by_contra h
    apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three at h
    norm_num at h
  have h3 := congr_arg (multiplicity 3) h
  -- we have multiplicity 3 (x * y) = multiplicity 3 x + multiplicity 3 y (whenever x * y ≠ 0)
  -- we get multiplicity 3 199! = multiplicity 3 199!! + multiplicity 3 (2 ^ 99) + multiplicity 3 99!
  rw [multiplicity_mul Nat.prime_three.prime (by rw [←h]; exact hfin_fact 199)] at h3
  -- the final equation is 97 = multiplicity 3 199!! + 0 + 48
  -- we conclude that multiplicity 3 199!! = 49
  rw [multiplicity_mul Nat.prime_three.prime, h2, h199f, h99f] at h3
  · omega
  rw [Nat.finiteMultiplicity_iff]
  norm_num