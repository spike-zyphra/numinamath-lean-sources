import Mathlib

open Finset

/- What is the smallest [positive](https://artofproblemsolving.com/wiki/index.php/Positive) [integer](https://artofproblemsolving.com/wiki/index.php/Integer) that can be expressed as the sum of nine consecutive integers, the sum of ten consecutive integers, and the sum of eleven consecutive integers? -/
theorem number_theory_704 : IsLeast { n | ∃a > 0, ∃b > 0, ∃c > 0,
  n = ∑ i ∈ range 9, (a + i) ∧
  n = ∑ i ∈ range 10, (b + i) ∧
  n = ∑ i ∈ range 11, (c + i)
  } 495 := by
    -- We use `solution 1`.
    simp_rw [sum_add_distrib (β := ℕ), sum_const, card_range, sum_range_id]
    ring_nf
    constructor
    case right =>
      rw [mem_lowerBounds]
      intro n
      rw [Set.mem_setOf_eq]
      intro ⟨a,ah,b,bh,c,ch,p,q,r⟩
      clear ah bh ch

      rw [q] at p r
      replace p : (9 * (a - 1): ℤ) = b * 10 := by linarith

      -- The relationship between $a,\ b$ suggests that $b$ is divisible by $9$.
      replace p := Dvd.intro (a - 1: ℤ) p
      apply IsRelPrime.dvd_of_dvd_mul_right (isRelPrime_iff_isCoprime.2 (by norm_num)) at p
      norm_cast at p

      -- Also, $10b -10 = 10(b-1) = 11c$, so $b-1$ is divisible by $11$.
      replace r : (11 * c: ℤ) = (b - 1) * 10 := by linarith

      replace r := Dvd.intro (c: ℤ) r
      apply IsRelPrime.dvd_of_dvd_mul_right (isRelPrime_iff_isCoprime.2 (by norm_num)) at r

      -- We find that the least possible value of $b = 45$, so the answer is $10(45) + 45 = 495$.
      save
      rw [dvd_def] at p
      revert p
      intro ⟨k, p⟩

      -- Check that `k ≥ 5` by listing the cases.
      have h: 5 ≤ k := by
        apply by_contradiction
        intro s
        rw [not_le] at s
        rw [p] at r
        interval_cases k <;> norm_num at r
      linarith

    case left =>
      rw [Set.mem_setOf_eq]
      refine ⟨51,Nat.zero_lt_succ 50,45,Nat.zero_lt_succ 44,40,Nat.zero_lt_succ 39,(by simp)⟩