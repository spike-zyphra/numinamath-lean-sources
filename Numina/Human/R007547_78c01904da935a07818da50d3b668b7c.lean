import Mathlib

/- Prove that there are no positive integers $n$ and $m>1$ such that $102^{1991}+103^{1991}=n^{m}$. -/
theorem number_theory_237147 (n m : ℕ) (hn : 0 < n) (hm : 1 < m) :
    ¬(102^1991 + 103^1991 = n^m) := by
 
  by_contra h

  -- It suffices to prove the statement over the integers by treating 102, 103 and n as integers
  -- rather than natural numbers.
  suffices  ¬∃ (n : ℤ), ∃ m : ℕ, n ≥ 1 ∧ m > 1 ∧ (102 : ℤ) ^ 1991 + (103 : ℤ) ^ 1991 = n ^ m by
      apply this
      use n
      use m
      constructor
      . exact Int.toNat_le.mp hn
      . constructor
        . omega
        . have lhs :   (102 : ℤ) ^ 1991 + (103 : ℤ) ^ 1991
                     = (@HAdd.hAdd ℕ ℕ ℕ instHAdd (102 ^ 1991) (103 ^ 1991)) := by zify
          rw [lhs]
          have claim (a b : ℕ) : a = b ↔ (a : ℤ) = (b : ℤ) := by zify
          rw [claim] at h
          have : ((n ^ m) : ℤ) = (@HPow.hPow ℕ ℕ ℕ instHPow n m) := by zify
          rw [this]
          exact h

  -- First, establish if a and b are integers and k is a natural number,
  -- then a^(2 * k + 3) + b^(2 * k + 3) can be factored as
  -- (a + b) * (a^(2 * k + 2) - a^(2 * k + 1) * b + a^(2 * k) * b^2 - ... - a * b^(2 * k + 1) + b^(2 * k + 2))
  -- We prove this by multiplying out the latter and note that it reduces to the former.
  have claim (a b : ℤ) (k : ℕ) : a ^ (2 * k + 3) + b ^ (2 * k + 3)
    = (a + b) * ∑ i ∈ Finset.range (2 * k + 3), ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ i) := by
      symm
      have ca :   a * (∑ i ∈ Finset.range (2 * k + 3), (-1) ^ i * a ^ (2 * k + 2 - i) * b ^ i)
                = a ^ (2 * k + 3) + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1)) := by
                  have : 1 ≤ 2 * k + 3 := by norm_num
                  rw [← Finset.sum_range_add_sum_Ico _ this, mul_add]
                  simp
                  rw [Finset.mul_sum]
                  ring_nf
                  rw [add_left_cancel_iff]
                  rw [Finset.sum_Ico_eq_sum_range]
                  have : 3 + k * 2 - 1 = 2 + k * 2 := by omega
                  rw [this]
                  apply Finset.sum_congr rfl
                  intro x
                  intro hx
                  have : a * a ^ (2 + k * 2 - (1 + x)) = a ^ (2 + k * 2 - x) := by
                    calc
                      _ = a ^ 1 * a ^ (2 + k * 2 - (1 + x)) := by rw [pow_one]
                      _ = a ^ (1 + (2 + k * 2 - (1 + x))) := by rw [← pow_add]
                      _ = a ^ (2 + k * 2 - x) := by have : (1 + (2 + k * 2 - (1 + x))) = 2 + k * 2 - x := by
                                                      calc
                                                        _ = 2 + k * 2 - (x + 1) + 1 := by simp [add_comm]
                                                        _ = 2 + k * 2 - x - 1 + 1 := by rw [Nat.sub_add_eq]
                                                        _ = 2 + k * 2 - x := by apply Nat.sub_add_cancel
                                                                                simp at hx
                                                                                omega
                                                    rw [← this]
                  ring_nf
                  rw [this]

      have cb :   b * (∑ i ∈ Finset.range (2 * k + 3), (-1) ^ i * a ^ (2 * k + 2 - i) * b ^ i)
                = b ^ (2 * k + 3) + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1)) := by
                  rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
                  simp
                  have : (-1) ^ (2 * k + 2) = 1 := by
                    calc
                      _ = (-1) ^ (2 * (k + 1)) := by ring
                      _ = ((-1) ^ 2) ^ (k + 1) := by apply pow_mul
                      _ = (1) ^ (k + 1) := by rw [neg_one_pow_two]
                      _ = _ := by apply one_pow
                  rw [this, add_comm]
                  ring_nf
                  rw [add_left_cancel_iff]
                  apply Finset.sum_congr rfl
                  ring_nf
                  simp

      have sumi :
              (  ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1))
               + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1)))
               = (∑ i ∈ Finset.range (2 * k + 2),   (((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1))
                                                 + ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1)))) := by exact Eq.symm Finset.sum_add_distrib
      calc
        _ =   a * (∑ i ∈ Finset.range (2 * k + 3), (-1) ^ i * a ^ (2 * k + 2 - i) * b ^ i)
            + b * (∑ i ∈ Finset.range (2 * k + 3), (-1) ^ i * a ^ (2 * k + 2 - i) * b ^ i) := by ring
        _ =   a ^ (2 * k + 3) + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1))
            + (b ^ (2 * k + 3) + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1))) := by rw [ca, cb]
        _ =   (a ^ (2 * k + 3) + b ^ (2 * k + 3))
            + (  ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1))
               + ∑ i ∈ Finset.range (2 * k + 2), ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1))) := by ring
        _ =   (a ^ (2 * k + 3) + b ^ (2 * k + 3))
            + (  ∑ i ∈ Finset.range (2 * k + 2),   (((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1))
                                                 + ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1)))) := by rw [sumi]
        _ =   (a ^ (2 * k + 3) + b ^ (2 * k + 3))
            + (  ∑ i ∈ Finset.range (2 * k + 2),  0) := by
                suffices ∀ i ∈ Finset.range (2 * k + 2),
                  (((-1) ^ (i + 1) * a ^ (2 * k + 2 - i) * b ^ (i + 1)) + ((-1) ^ i * a ^ (2 * k + 2 - i) * b ^ (i + 1))) = 0 by
                    refine add_left_cancel_iff.mpr ?_
                    exact Finset.sum_congr rfl this
                intro i hi
                ring_nf
        _ = _ := by simp


  -- Apply the above result to a = 102, b = 103, and k = 994 to obtain that
  -- 102 ^ 1991 + 103 ^ 1991 = (102 + 103) * (102^1990 - 102^1989 * 103 + 102^1987 * 103^2 - ... - 102 * 103^1989 + 103^1990).
  have factored := claim 102 103 994
  intro h
  obtain ⟨ n , m, hnlb, hmlb, heq ⟩ := h
  have : 1991 = 2 * 994 + 3 := by norm_num
  rw [this] at heq
  rw [← this] at factored heq
  clear this
  have : 1990 = 2 * 994 + 2 := by norm_num
  rw [← this] at factored
  clear this
  rw [factored] at heq

  -- Note that 5 divides (102 + 103) * (102^1990 - 102^1989 * 103 + 102^1987 * 103^2 - ... - 102 * 103^1989 + 103^1990)
  -- since 102 + 103 = 205, which is a multiple of 5.
  have lhsD5 : 5 ∣ (102 + 103) * ∑ i ∈ Finset.range 1991, (-1) ^ i * 102 ^ (2 * 995 - i) * 103 ^ i := by
    simp
    apply dvd_mul_of_dvd_left
    decide
  have rhsD5 : 5 ∣ n ^ m := by
    rw [← heq]
    exact lhsD5

  -- Thus, 5 divides n since (102 + 103) * (102^1990 - 102^1989 * 103 + 102^1987 * 103^2 - ... - 102 * 103^1989 + 103^1990) = n^m.
  have nD5 : 5 ∣ n := by apply Prime.dvd_of_dvd_pow
                         refine Int.prime_iff_natAbs_prime.mpr ?hp.a
                         norm_cast
                         apply rhsD5

  have : ∃ k : ℤ, n = 5 * k := by exact nD5
  obtain ⟨ k, hk ⟩ := this
  rw [hk] at heq
  have : (102 : ℤ) + 103 = 5 * 41 := by norm_num
  rw [this] at heq

  -- Note that m ≥ 2 by assumption. Hence, we can write m as m' + 2 for some
  -- natural number m'.
  have : ∃ m' : ℕ, m = m' + 2 := by exact Nat.exists_eq_add_of_le' hmlb
  obtain ⟨ m', hm' ⟩ := this
  -- Replace m in terms of m'.
  rw [hm'] at heq
  have : (5 * k) ^ (m' + 2) = 5 * (5 * (k ^ 2 * (5 * k) ^ m')) := by ring_nf

  -- The rest then follows mechanically.
  omega
