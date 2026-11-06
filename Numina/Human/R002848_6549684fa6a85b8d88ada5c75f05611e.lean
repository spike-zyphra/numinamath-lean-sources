import Mathlib

import Mathlib.Data.ZMod.Defs
/- 5. Find all pairs of positive integers $(m, n)$ such that $6^{m} + 2^{n} + 2$ is a perfect square. -/
theorem number_theory_121670 (m n : ℕ) (hm : 0 < m) (hn : 0 < n):
  (∃ k : ℤ, k^2 = 6^m + 2^n + 2) ↔ (m, n) = (1, 3) := by
  simp
  -- First, prove that no solutions but (1,3) exist
  apply Iff.intro; {

    intro h
    cases h with | intro k h =>
    -- Note that k ≠ 0
    have h0: k ≠ 0:= by {
      intro h0
      rw [h0] at h
      revert h
      apply Int.ne_of_lt
      apply Int.add_pos_of_pos_of_nonneg (Int.add_pos_of_nonneg_of_pos _ _)
      repeat simp
    }
    -- either m or n equals 1:
    have hmn: m = 1 ∨ n = 1 := by {
      by_contra hc
      simp at hc
      apply congrArg (multiplicity 2) at h
      revert h
      simp
      -- multiplicity of 2 in k^2 must be even
      rw [FiniteMultiplicity.multiplicity_pow]; {
        have hmr: ∃ r, m = r + 2 := by {
          match m with
          | 0 => simp at hm
          | 1 => simp at hc
          | r + 2 => use r
        }
        have hnt: ∃ t, n = t + 2 := by {
          match n with
          | 0 => simp at hn
          | 1 => simp at hc
          | t + 2 => use t
        }
        cases hmr with | intro r hr =>
        cases hnt with | intro t ht =>
        -- but if both m and n are at least 2, 4 divides 6^m + 2^n, so multiplicity of 2 in 6^m + 2^n + 2 is 1
        have h1: multiplicity 2 ((6:ℤ) ^ m + 2 ^ n + 2) = 1 := by {
          rw[FiniteMultiplicity.multiplicity_eq_iff]
          {
            rw [hr, ht, pow_add, pow_add]
            simp
            apply And.intro; {
              use 6 ^ r * 18 + 2 ^ t * 2
              ring
            }; {
              rw [Int.dvd_add_right]; norm_num
              use 6 ^ r * 9 + 2 ^ t
              ring
            }
          }
          apply FiniteMultiplicity.of_not_isUnit; rw[Int.isUnit_iff]; simp
          apply Int.ne_of_gt
          apply Int.add_pos_of_pos_of_nonneg (Int.add_pos_of_nonneg_of_pos _ _)
          repeat simp
        }
        rw [h1]
        simp
      }
      norm_num
      apply FiniteMultiplicity.of_not_isUnit _ h0
      rw [Int.isUnit_iff]; simp
    }
    -- if m = 1, then n = 3
    cases hmn with
    |inl hmn => {
      apply And.intro hmn
      rw [hmn] at h
      ring_nf at h
      apply congrArg Int.natAbs at h
      rw [Int.natAbs_pow] at h
      have hk: ∃ kn: ℕ, k.natAbs = kn := by use k.natAbs
      cases hk with | intro kn hk =>
      rw [hk] at h
      -- cases n = 1, n = 2 yield 10 and 12, which are not squares
      match n with
      | 0 => simp at hn
      | 1 => {
        simp at h
        by_contra
        match kn with
        |0 => simp at h
        |1 => simp at h
        |2 => simp at h
        |3 => simp at h
        |k+4 =>
          rw[Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add, <-Nat.add_assoc] at h
          simp! at h
      }
      |2 => {
        simp at h
        by_contra
        match kn with
        |0 => simp at h
        |1 => simp at h
        |2 => simp at h
        |3 => simp at h
        |k+4 =>
          rw[Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add, <-Nat.add_assoc] at h
          simp! at h
      }
      |3 => rfl
      -- for n > 3, 6^m + 2^n + 2 equals (1 + 2 * 2^(n-4)) * 8, so its 8 times an odd number, can't be a square
      |n + 4 =>
        by_contra
        have hh: (1 + 2 * 2^n) * 8 = kn^2 := by {
          convert h.symm using 1
          rw [Nat.add_mul, Nat.mul_comm 2, Nat.mul_assoc, pow_add]
          norm_num
          apply Eq.symm
          rw [Int.natAbs_eq_iff]
          left
          simp
        }
        apply congrArg (multiplicity 2) at hh
        revert hh
        rw[FiniteMultiplicity.multiplicity_pow, multiplicity_mul]; {
          simp
          have h0: (multiplicity 2 (1 + 2 * 2 ^ n)= 0) := by {
            rw [multiplicity_eq_zero]
            simp
          }
          rw[h0]
          have h8: multiplicity 2 8 = 3 := by
            rw [FiniteMultiplicity.multiplicity_eq_iff]
            norm_num
            apply FiniteMultiplicity.of_not_isUnit
            norm_num
            norm_num
          rw [h8]
          simp
          have h32: ¬ 2 ∣ 3 := by
            norm_num
          rw[Dvd.dvd, Nat.instDvd] at h32
          simp at h32
          specialize h32 (multiplicity 2 kn)
          exact h32
        }; {
          rw [←Nat.prime_iff]
          norm_num
        }; {
          apply FiniteMultiplicity.of_not_isUnit; norm_num
          simp

        }; {
          rw [←Nat.prime_iff]
          norm_num
        }; {
          apply FiniteMultiplicity.of_not_isUnit
          norm_num
          rw[←hk]
          simp
          exact h0
        }
    }
    -- if n = 1, there are no solutions, because there are no solutions mod 7
    |inr hmn => {
      rw [hmn]
      simp

      rw [hmn] at h
      ring_nf at h
      have h7: ∃ k7: ZMod 7, k = k7 := by
        use k
      cases h7 with | intro k7 h7 =>

      have hmod: ∀ r t:ℤ, (r = t)→ ( r : ZMod 7) = t := by {
        intro r t hrt
        rw [hrt]
      }
      apply hmod at h
      simp at h
      have hneg: (k ^ 2: ZMod 7) = 4 + (-1) ^ m  := by
        rw [h]; rfl
      revert hneg
      rw [h7]
      cases neg_one_pow_eq_or (ZMod 7) m with
      |inl h1 => {
        rw[h1]
        match k7 with
          | 0 => norm_num; simp!
          | 1 => norm_num; simp!
          | 2 => norm_num; simp!
          | 3 => norm_num; simp!
          | 4 => norm_num; simp!
          | 5 => norm_num; simp!
          | 6 => norm_num; simp!
      }
      |inr h1 => {
        rw [h1]
        match k7 with
          | 0 => norm_num; simp!
          | 1 => norm_num; simp!
          | 2 => norm_num; simp!
          | 3 => norm_num; simp!
          | 4 => norm_num; simp!
          | 5 => norm_num; simp!
          | 6 => norm_num; simp!
      }
    }
  }; {
    -- Finally, we have to check that (1,3) is actually a solution
    intro hmn
    cases hmn with | intro hm hn =>
    rw[hm, hn]
    use 4
    ring
  }