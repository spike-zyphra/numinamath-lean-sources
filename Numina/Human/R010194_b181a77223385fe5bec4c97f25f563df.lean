import Mathlib


/-- How many of the first ten numbers of the sequence 121,11211,1112111,… are prime numbers?
    (A) 0(B) 1(C) 2(D) 3(E) 4 -/
theorem number_theory_94117 (n k : ℕ) (hn : n = 10^k + ∑ i ∈ Finset.range (2 * k + 1), 10^i)
    (hpos : k > 0) : ¬ n.Prime := by
  -- There are 0 such primes: Let n be such a prime.
  intro hp
  -- The sequence is defined in such a way that the k-th term equals 10^k + 10^0 + 10^1 + ... + 10^(2k).
  -- But by distributivity, this equals (10^k + 1) * (10^0 + ... + 10^k).
  have : n = (10 ^ k + 1) * ∑ i ∈ Finset.range (k + 1), 10^i := by
    rw[hn, Finset.mul_sum]
    conv => enter[2,2,i]; rw[add_mul, ← pow_add, one_mul]; left; rw[add_comm]
    rw[two_mul, add_assoc, add_comm k]
    rw[Finset.sum_add_distrib, Finset.sum_range_add, ← add_left_comm]
    conv => right; rw[add_comm]
    congr 1
    rw[Finset.sum_range_succ', add_comm]
    congr
    · ext x; ring
    · exact (Nat.zero_add k).symm
  rw[this] at hp
  -- Since k > 0, neither of these factors can be 1, and n cannot be prime.
  apply Nat.not_prime_mul _ _ hp
  · simp
  · change 0 < k at hpos
    rw[← Nat.exists_eq_add_one] at hpos
    obtain ⟨j,rfl⟩ := hpos
    rw[Finset.sum_range_succ', Finset.sum_range_succ']
    simp