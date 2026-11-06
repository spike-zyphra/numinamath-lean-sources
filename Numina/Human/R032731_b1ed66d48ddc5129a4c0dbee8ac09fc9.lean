import Mathlib

open Finset

/- Which are the arithmetic sequences in which the sum of the first $n$ elements is a square number for every $n$? -/
theorem number_theory_214851 (a d : ℝ) :
    (∀ n : ℕ, ∃ m : ℕ, m^2 = ∑ i in range n, (a + d * i)) ↔ (∃ b : ℕ, a = b ^ 2 ∧ d = 2 * b ^ 2) := by
  -- Show that the sum of the first n elements of the arithmetic sequence is equal to
  -- (a + (n - 1) * d / 2) * n.
  have hsum n : ∑ i ∈ range n, (a + d * i) = (a + (n - 1) * d / 2) * n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  symm
  constructor
  -- Show that a = b^2 and d = 2 * b^2 for some b ∈ ℕ implies that
  -- the sum of the first n elements is a square number.
  · intro ⟨b, ha, hd⟩
    subst a d
    intro n
    -- Show that the sum is equal to (b * n)^2.
    use b * n
    rw [hsum]
    simp [mul_pow]
    ring
  -- Assume that the sum of the first n elements is a square number.
  -- Show that there exists b ∈ ℕ such that a = b^2 and d = 2 * b^2.
  intro h
  -- The sum of 1 element is a = b^2 for some b ∈ ℕ.
  have ⟨b, hb⟩ := h 1
  simp at hb
  -- We have a = b^2. Show that d = 2 * b^2.
  use b
  subst a
  simp only [true_and]
  -- Show that d is a natural number.
  have ⟨d', hd1⟩ : ∃ d' : ℕ, d = d' := by
    -- Prove that 0 ≤ d.
    have hd0 : 0 ≤ d := by
      -- Assume that d < 0 and derive a contradiction.
      -- More specifically, show that d < 0 implies that there exists n
      -- such that the sum of the first n elements is not a square number.
      contrapose! h
      -- Find n ∈ ℕ such that n > 2 * b^2 / -d + 1.
      have ⟨n, hn⟩ := exists_nat_gt (2 * b^2 / -d + 1)
      use n
      intro m
      -- Show that the sum of the first n elements is negative. It will imply
      -- that this sum is not a square of any number.
      apply ne_of_gt
      rw [hsum]
      apply lt_of_lt_of_le _ (pow_two_nonneg _)
      -- We need to show that (b^2 + (n - 1) * d / 2) * n < 0.
      -- It is sufficient to show that b^2 + (n - 1) * d / 2 < 0 and n > 0.
      apply mul_neg_of_neg_of_pos
      · suffices 2 * b ^ 2 < (n - 1) * (-d) by linarith
        -- b^2 + (n - 1) * d / 2 < 0 because n - 1 > 2 * b^2 / -d and d < 0.
        apply lt_of_le_of_lt (b := (2 * b ^ 2 / -d + 1 - 1) * (-d))
        · simp only [add_sub_cancel_right]
          rw [div_mul_cancel₀ _ (by linarith)]
        · gcongr
          linarith
      · apply lt_trans _ hn
        -- 0 < n because 0 < 2 * b^2 / -d + 1 < n.
        apply add_pos_of_nonneg_of_pos _ zero_lt_one
        apply div_nonneg (by positivity) (by linarith)
    -- Consider the sum of the first two elements:
    -- a + (a + d) = m^2 for some m ∈ ℕ.
    -- a = b^2 ∈ ℕ and d ≥ 0 so there exists d' ∈ ℕ such that d = d'.
    have ⟨m, hm⟩ := h 2
    simp [sum_range_succ] at hm
    use m ^ 2 - 2 * b ^ 2
    rify [show (2 : ℝ) * b ^ 2 ≤ m ^ 2 by linarith]
    linarith
  -- Show that d' is even, i.e., there exists e ∈ ℕ such that d' = 2 * e.
  have ⟨e, he⟩ : ∃ e, d' = 2 * e := by
    -- Consider the sum of the first 4 elements:
    -- m^2 = b^2 * 4 + d' * 6 for some m ∈ ℕ.
    have ⟨m, hm⟩ := h 4
    rw [hsum, add_mul, hd1] at hm
    ring_nf at hm
    norm_cast at hm
    -- It is enough to show that 4 divides d' * 6.
    -- If 4 ∣ d' * 6 then 2 ∣ d'.
    suffices 4 ∣ d' * 6 by
      have : 2 ∣ d' := by omega
      exact this
    -- It is enough to show that 2 ∣ m^2.
    -- If 2 ∣ m^2 then 2 ∣ m (because 2 is prime) and hence 4 ∣ m^2.
    -- 4 ∣ m^2 implies that 4 ∣ b^2 * 4 + d' * 6, so 4 ∣ d' * 6.
    suffices 2 ∣ m ^ 2 by
      have : 2 ∣ m := Nat.prime_two.dvd_of_dvd_pow this
      have : 4 ∣ m ^ 2 := by rwa [show 4 = 2 ^ 2 by norm_num, Nat.pow_dvd_pow_iff (by norm_num)]
      omega
    -- 2 ∣ m^2 because m^2 = 2 * (b^2 * 2 + d' * 3).
    omega
  -- If e = b^2 then d = 2 * e = 2 * b^2.
  by_cases heb : e = b ^ 2
  · simp [hd1, he, heb]
  -- Assume that e ≠ b^2.
  -- Show that there exists a prime number p such that p does not divide |b^2 - e|.
  have ⟨p, hp, hp1⟩ : ∃ p, Nat.Prime p ∧ ¬ p ∣ (b ^ 2 - e : ℤ).natAbs := by
    -- Find a prime number p such that p ≥ |b^2 - e| + 1.
    have ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes ((b ^ 2 - e : ℤ).natAbs + 1)
    use p, hp
    -- p does not divide |b^2 - e| because p > |b^2 - e| and |b^2 - e| ≠ 0.
    apply Nat.not_dvd_of_pos_of_lt _ (by linarith)
    rw [Int.natAbs_pos]
    contrapose! heb
    linarith
  zify at hp1
  -- Derive a contradiction: show that p divides |b^2 - e|.
  contrapose! hp1
  -- Consider the sum of the first p elements:
  -- m^2 = b^2 * p - p * e + p^2 * e for some m ∈ ℕ.
  have ⟨m, hm⟩ := h p
  rw [hsum, hd1, he] at hm
  push_cast at hm
  ring_nf at hm
  -- p divides |b^2 - e| is equivalent to p ∣ b^2 - e.
  rw [dvd_abs]
  replace hm : (m : ℤ) ^ 2 = b^2 * p - p * e + p^2 * e := by
    rify
    exact hm
  -- It is enough to show that p^2 ∣ m^2.
  suffices p ^ 2 ∣ m ^ 2 by
    zify at this
    rw [hm] at this
    -- If p^2 ∣ m^2 then p^2 ∣ (b^2 - e) * p.
    rw [Int.dvd_add_left (by use e)] at this
    have ⟨k, hk⟩ := this
    use k
    have hp0 : (p : ℤ) ≠ 0 := by
      norm_cast
      exact hp.ne_zero
    -- We get that p divides b^2 - e.
    rw [← mul_left_inj' hp0]
    linarith
  -- To show that p^2 ∣ m^2, show that p ∣ m.
  rw [Nat.pow_dvd_pow_iff two_ne_zero]
  -- p is a prime number, so it is enough to show that p ∣ m^2.
  apply hp.dvd_of_dvd_pow (n := 2)
  zify
  -- p ∣ m^2 because m^2 = p * (b^2 - e + p * e).
  use b ^ 2 - e + p * e
  linear_combination hm