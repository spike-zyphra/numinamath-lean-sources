import Mathlib

/- Let's prove that for every natural number $k$, there exists a natural number $n$ such that $\left(n^{2}+1\right)$ is divisible by the $k$-th power of 5. -/
theorem number_theory_162574 (k : ℕ) :
    ∃ n : ℕ, 5^k ∣ (n^2 + 1) := by

  -- It is easier to work in ℤ than in ℕ, so we will prove the result in ℤ
  -- and then use the fact that ℕ is a subring of ℤ.
  suffices ∃ n : ℤ, n >= 0 ∧ 5 ^ k ∣ (n ^ 2 + 1) by
    obtain ⟨n, h⟩ := this
    use n.toNat
    obtain ⟨hn, r, hr⟩ := h
    use r.toNat
    have : 0 ≤ r := by
      by_contra!
      have : 5 ^ k * r < 0 := by apply mul_neg_of_pos_of_neg (by simp) this
      have := Int.add_pos_of_nonneg_of_pos (sq_nonneg n) (Int.zero_lt_one)
      linarith
    zify
    simp only [Int.ofNat_toNat, Int.max_eq_left this, Int.max_eq_left hn]
    exact hr

  -- We prove the result by induction on k.
  induction' k using Nat.strong_induction_on with k ih
  rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
  · -- If k = 0, then we can take n = 0.
    rw [Nat.lt_one_iff] at hlt
    rw [hlt]
    use 0
    simp
  · -- If k = 1, then we can take n = 2.
    rw [heq]
    use 2
    simp
  · -- If k > 1, we have that 5^(k-1) ∣ (n^2 + 1) for some n, and prove that 5^k ∣ ((n^5)^2 + 1).
    let r := k - 1
    have : 0 < r := Nat.zero_lt_sub_of_lt hgt
    obtain ⟨n, hn, m, hm⟩ := ih r (Nat.sub_one_lt_of_lt hgt)
    use n^5
    constructor
    · -- n^5 is positive if n is positive.
      exact pow_nonneg hn 5
    · -- We use that (n^5)^2 = (n^2)^5, write n^2 as 5^r * m - 1, and simplify.
      have : (5 ^ r * m - 1) ^ 5 + 1 =
          5 ^ (r + 1) * (5 ^ (4 * r - 1) * m ^ 5 - 5 ^ (3 * r) * m ^ 4 + 2 * 5 ^ (2 * r) * m ^ 3
            - 2 * 5 ^ r * m ^ 2 + m) := by
        calc (5 ^ r * m - 1) ^ 5 + 1 =
            5 ^ (5 * r) * m ^ 5 - 5 * 5 ^ (4 * r) * m ^ 4 + 2 * 5 * 5 ^ (3 * r) * m ^ 3
            - 2 * 5 * 5 ^ (2 * r) * m ^ 2 + 5 * 5 ^ r * m := by rw [← sub_eq_zero]; ring_nf
        _ = 5 ^ (r + 1) * 5 ^ (4 * r - 1) * m ^ 5 - 5 ^ (r + 1) * 5 ^ (3 * r) * m ^ 4 + 5 ^ (r + 1) * 2
            * 5 ^ (2 * r) * m ^ 3 - 5 ^ (r + 1) * 2 * 5 ^ r * m ^ 2 + 5 ^ (r + 1) * m := by
            rw [(by rw [← pow_add]; congr; rw [add_assoc, add_comm 1, Nat.sub_add_cancel (by linarith)]; ring :
                (5 : ℤ) ^ (r + 1) * 5 ^ (4 * r - 1) = 5 ^ (5 * r))]
            ring_nf
        _ = 5 ^ (r + 1) * (5 ^ (4 * r - 1) * m ^ 5 - 5 ^ (3 * r) * m ^ 4 + 2 * 5 ^ (2 * r) * m ^ 3
            - 2 * 5 ^ r * m ^ 2 + m) := by ring_nf
      -- We substitute this into the divisibility condition and he thesis follows.
      rw [← pow_mul, mul_comm, pow_mul, (by rw [← hm]; simp : n ^ 2 = 5 ^ r * m - 1), this]
      use (5 ^ (4 * r - 1) * m ^ 5 - 5 ^ (3 * r) * m ^ 4 + 2 * 5 ^ (2 * r) * m ^ 3 - 2 * 5 ^ r * m ^ 2 + m)
      congr; omega