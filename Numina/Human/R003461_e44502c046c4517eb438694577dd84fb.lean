import Mathlib

open BigOperators

-- Lemma: The sum of m consecutive natural numbers starting from k is ((2*k + m - 1) * m) / 2.
lemma lemma_1 (k m : ℕ) : ∑ i in Finset.Ico k (k+m), i = ((2*k+m-1)*m)/2 := by
  -- We prove the lemma by induction on m.
  induction m with
  | zero =>
    -- Base case: m = 0. The sum over an empty range is 0, and the right-hand side is also 0.
    simp
  | succ m hm =>
    -- Inductive step: Assume the lemma holds for m, show for m + 1.
    calc
      -- The sum from k to k + (m + 1) is the sum from k to k + m, plus the next term (k + m).
      _ = ∑ i ∈ Finset.Ico k ((k + m) + 1), i := by
        rw [add_assoc]
      _ = (∑ i ∈ Finset.Ico k (k + m), i) + (k+m) := by
        rw [Finset.sum_Ico_succ_top]
        linarith
      _ = _ := by
        -- Substitute the inductive hypothesis for the sum up to m.
        rw [hm]
        simp
        -- We now split into cases depending on whether m is odd or even.
        by_cases hodd : Odd m
        · rcases hodd with ⟨m1, hm1⟩
          -- Case 1: m is odd, so m = 2*m1 + 1 for some m1.
          rw [hm1]
          -- We show that the formula simplifies correctly in this case.
          have : (2 * k + (2 * m1 + 1) - 1) * (2 * m1 + 1) / 2 = (k+m1)*(2*m1+1) := by
            rw [mul_comm]
            rw [Nat.mul_div_assoc]
            · have : ((2 * k + (2 * m1 + 1) - 1) / 2) = k+m1 := by omega
              rw [this]
              rw [mul_comm]
            · omega
          rw [this]
          rw [Nat.mul_div_assoc]
          · have : (2 * m1 + 1 + 1) / 2 = m1 + 1 := by omega
            rw [this]
            ring
          · omega
        · simp at hodd
          rcases hodd with ⟨m1, hm1⟩
          ring_nf at hm1
          -- Case 2: m is even, so m = 2*m1 for some m1.
          rw [hm1]
          rw [Nat.mul_div_assoc]
          · have : m1 * 2 / 2 = m1 := by omega
            rw [this]
            -- We show that the formula simplifies correctly in this case as well.
            have : (2 * k + m1 * 2) * (m1 * 2 + 1) / 2 = (k+m1)*(m1*2+1) := by
              rw [mul_comm]
              rw [Nat.mul_div_assoc]
              · have : (2 * k + m1 * 2) / 2 = k+m1 := by omega
                rw [this]
                rw [mul_comm]
              · omega
            rw [this]
            -- Further subcases: m1 = 0 or m1 ≥ 1, handled by omega.
            by_cases hmzero : m1 = 0
            · rw [hmzero]
              omega
            · have : m1 ≥ 1 := by omega
              let m2 := m1 - 1
              have hsub : m1 = m2 + 1 := by omega
              have : 2 * k + m1 * 2 - 1 = 2 * k + m2 * 2 + 1 := by omega
              rw [this]
              rw [hsub]
              ring_nf
          · omega

-- The sum of m consecutive natural numbers is equal to a prime number p. What can m be?
theorem number_theorem_184824 (k m p : ℕ)(hm : m ≥ 1)(hp : p.Prime)(heq : ∑ i in Finset.Ico k (k+m), i = p) : m = 1 ∨ m = 2 ∨ m = 3 := by
  -- Substitute the closed formula for the sum from lemma_1.
  rw [lemma_1 k m] at heq
  -- Split into cases depending on whether m is odd or even.
  by_cases hodd : Odd m
  · rw [mul_comm] at heq
    rcases hodd with ⟨m1, hm1⟩
    -- If m is odd, then m divides the sum, so m must be 1 or p.
    have : 2 ∣ (2*k+m-1) := by
      rw [hm1]
      omega
    rw [Nat.mul_div_assoc m this] at heq
    rw [← heq] at hp
    -- Since p is prime, either m = 1 or the other factor is 1.
    have := Nat.prime_mul_iff.mp hp
    omega
  · simp at hodd
    have : 2∣m := by exact even_iff_two_dvd.mp hodd
    rw [Nat.mul_div_assoc (2 * k + m - 1) this] at heq
    rw [← heq] at hp
    -- If m is even, 2 divides m, so the other factor must be 1 or p.
    have := Nat.prime_mul_iff.mp hp
    rcases this with h1 | h2
    · omega
    · omega
