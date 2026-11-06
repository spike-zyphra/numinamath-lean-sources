import Mathlib

/-- If $4n+1, 6n+1$ are both perfect squares,
    then the smallest positive integer value of $n$ is 20. -/
theorem number_theory_191927 :
    IsLeast {n | 0 < n ∧ (∃ k, k^2 = 4 * n + 1) ∧ ∃ m, m^2 = 6 * n + 1} 20 := by
  constructor
  -- 20 clearly fulfills the conditions, since 81 and 121 are squares.
  -- We show that that it is the smallest number.
  · simp only [exists_and_right, Set.mem_setOf_eq, Nat.ofNat_pos, Nat.reduceMul, Nat.reduceAdd,
    true_and]
    exact ⟨⟨9,rfl⟩,⟨11,rfl⟩⟩
  · rintro n ⟨pos, ⟨k,ksq⟩, ⟨m,msq⟩⟩
  -- Let k'^2 = 4n+1, m'^2 = 6n+1. Then k,m must be odd since their squares are.
  -- Hence, replace k' by 2k+1, m' by 2m+1.
    obtain ⟨k,rfl⟩ : Odd k := by
      apply Nat.Odd.of_mul_left (n := k)
      rw[← sq, ksq]
      exists 2 * n
      ring
    obtain ⟨m,rfl⟩ : Odd m := by
      apply Nat.Odd.of_mul_left (n := m)
      rw[← sq, msq]
      exists 3 * n
      ring
    -- We are given the two equations (2k+1)^2 = 4n+1, (2m+1)^2 = 6n+1.
    have : 6 * n + 1 = 4 * m * (m + 1) + 1 := by linarith
    -- The latter implies 3n = 2 m (m + 1).
    have : 3 * n = 2 * m * (m + 1) := by linarith
    -- But m(m+1) is even, such that
    obtain ⟨m', eq⟩ := m.even_mul_succ_self
    rw[mul_assoc, eq] at this
    -- n is divisible by 4.
    obtain ⟨n,rfl⟩ : 4 ∣ n := by
      apply Nat.Coprime.dvd_of_dvd_mul_left (m := 3) (by norm_num)
      exists m'
      linarith
    -- So it remains to check the cases n = 4,8,12,16.
    suffices h : 5 ≤ n by linarith
    have : 0 < n := by linarith
    by_contra!
    interval_cases n
    -- If n = 4, 4n+1 = 17 would be a square, but it is prime, contradiction.
    · simp at ksq
      have : Nat.Prime 17 := by norm_num
      rw[← ksq, Nat.prime_iff] at this
      apply not_prime_pow (by norm_num) this
    -- If n = 8, 4n+1=33 would be a square, but it is squarefree.
    · simp at ksq
      have : Squarefree 33 := by
        rw[Nat.squarefree_mul (m := 3) (n := 11) (by norm_num)]
        constructor <;>
         {apply Prime.squarefree
          rw[← Nat.prime_iff]
          norm_num}
      rw[← ksq, Nat.squarefree_pow_iff] at this
      · have := this.2; contradiction
      · intro eq; rw[eq] at ksq; linarith
      · simp
    -- If n = 12, 6n+1 = 73 would be a square, but it is prime.
    · simp at msq
      have : Nat.Prime 73 := by norm_num
      rw[← msq, Nat.prime_iff] at this
      apply not_prime_pow (by norm_num) this
    -- Last, if n = 16, 6n+1=97 is also prime, hence not a square.
    · simp at msq
      have : Nat.Prime 97 := by norm_num
      rw[← msq, Nat.prime_iff] at this
      apply not_prime_pow (by norm_num) this