import Mathlib

/- Let $n$ be a positive integer such that ${{n}^{1800}}={{60}^{n}}$. Find the value of $n$. -/
theorem algebra_6957 (n : ℕ) (hn : 0 < n) : n ^ 1800 = 60 ^ n ↔ n = 3600 := by
  constructor
  · intro h

    -- lemma that help to prove ∃ k, n = 60^k
    have h0 (n a b: ℕ)(hn: 0<n)(ha:0<a)(hb:0<b)(h: n^a=60^b) :
        ∃ k, n = 60^k := by
      have h_fact_3 : (60 ^ b).factorization 3 = b := by
        simp [Nat.factorization_pow, show Nat.factorization 60 3 = 1 by native_decide]
      simp [← h, Nat.factorization_pow] at h_fact_3
      obtain ⟨k, hk⟩ : a ∣ b := Dvd.intro _ h_fact_3
      rw [hk, mul_comm, pow_mul] at h
      use k
      apply Nat.pow_left_injective (by linarith) h

    -- we can use the lemma above to prove that n=60^k
    have h1: ∃ k, n = 60^k := by
      exact h0 n 1800 n hn (by nlinarith) hn h

    rcases h1 with ⟨k, hk⟩

    -- simplification h into 1800k = 60^k
    rw [hk, ← pow_mul, pow_right_inj₀] at h
    all_goals try nlinarith

    -- for all k ≥ 3, we have 60^k > 1800, which has contradiction with h
    have h2: k < 3 := by
      rw [lt_iff_not_ge]
      intro h3
      let p := k-2

      have h4: k * 1800 < 60^k := by
        clear * - h3
        induction' h3 with k h5 h6
        . nlinarith
        have h7: 60^k*60 = 60^k+60^k*59 := by nlinarith
        simp [Nat.pow_succ, add_mul, h7]
        apply Nat.add_lt_add
        . exact h6
        have h8: 60^k > 1800 := by
          calc 60^k > 60^2 := by
                apply Nat.pow_lt_pow_right
                nlinarith
                simp at h5
                nlinarith
              _ = 3600 := by nlinarith
              _ > 1800 := by nlinarith
        calc 60^k*59 ≥ 60^k := by
                  apply Nat.le_mul_of_pos_right
                  nlinarith
             _ > 1800 := by exact h8

      nlinarith

    -- try case k = 0, 1, 2, which only k=2 is the answer, in which case n=3600
    interval_cases k
    all_goals nlinarith
  · intro h
    -- n^1800 = 60^(2*1800)
    nth_rewrite 2 [show n = 2 * 1800 by nlinarith]
    -- (60^2)^1800 = 60^(2*1800)
    rw [show n = 60^2 by nlinarith]
    rw [pow_mul]
