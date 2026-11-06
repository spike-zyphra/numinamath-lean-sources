import Mathlib

theorem number_theory_152796 : ∑ x in (Nat.divisors (2^2007)), x = 2^(2008)-1 := by 
  
  --We know that the divisors of 2^k have the form 2^i where 0 ≤ i ≤ k.
  rw [Nat.divisors_prime_pow (by norm_num)]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  have : 2007 + 1 = 2008 := by norm_num
  rw [this]

  --Now we prove that 1+2+...+(2^a-1) is equal to (2^(a+1)-1).
  have : ∀ n:ℕ,  ∑ x ∈ Finset.range n, 2 ^ x = 2 ^ n - 1 := by 
    intro n
    induction' n with n hn

    simp

    rw [Finset.sum_range_succ, hn]
    ring_nf
    rw [mul_two]
    have : 0 ≤ 2^n := by positivity
    omega
    

  specialize this 2008
  exact this
  