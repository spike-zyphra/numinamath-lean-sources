import Mathlib

/-
How many positive divisors does $2022^{2022}$ have?
-/

theorem number_theory_629554 (n:ℕ) (hn: n=2022^2022):
n.divisors.card = 2023^3 := by
  have npos: 0 < n := by 
    rw [hn]
    positivity
  have nne0: n ≠ 0 := by exact Nat.not_eq_zero_of_lt npos

  --The number of divisors equals to prod of one plus the multipilicty of all prime facotrs.
  rw [Nat.card_divisors]
  simp only [hn,Nat.factorization_pow]
  --The prime factors of 2022^2022 are same as those of 2002.
  have : (2022^2022).primeFactors = (2022).primeFactors := by 
    rw [Nat.primeFactors_pow]
    norm_num
  rw [this] 
  -- now we need to calculate the primeFactors of 2022.
  have : (2022).primeFactors = {2,3,337} := by native_decide
  rw [this]

  simp only [Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul,Finset.mem_insert,Nat.reduceEqDiff,Finset.mem_singleton,or_self,not_false_eq_true,Finset.prod_insert,Finset.prod_singleton]

  --Use the prime factorization of 2022, which is 2022 = 2 * 3 * 337.
  have t1 : (Nat.factorization 2022) 2 = 1 := by native_decide
  have t2 : (Nat.factorization 2022) 3 = 1 := by native_decide
  have t3 : (Nat.factorization 2022) 337 = 1 := by native_decide
  rw [t1,t2,t3]
  
  norm_num

  exact nne0
