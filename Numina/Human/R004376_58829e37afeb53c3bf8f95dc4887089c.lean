import Mathlib

open Finset

/- Example 9 Proof: In the sequence with the general term formula $a_{n}=1^{1}+2^{2}+3^{3}+\cdots+n^{n}(n \in \mathrm{N})$, there are infinitely many even composite numbers. -/
theorem number_theory_258161 {a : ℕ → ℕ}
    (ha : ∀ n, a n = ∑ i ∈ Icc 1 n, i ^ i) :
    {n | Even (a n) ∧ ¬Nat.Prime (a n) ∧ a n ≠ 1}.Infinite := by
  -- proving that for all N, there is n ≥ N with a n being even composite is enough
  simp_rw [← Nat.Ico_succ_right] at ha
  rw [← Nat.frequently_atTop_iff_infinite]
  simp [Filter.Frequently]
  rintro n
  -- use 4 * (n + 1) for each n
  use 4 * (n + 1)
  -- we will prove a (4 * (n + 1)) is even by using induction on (n + 1)
  have h : Even (a (4 * (n + 1))) := by
    generalize n + 1 = k
    induction' k with m hm
    -- for k = 0, obvious
    . simp [ha]
    -- otherwise write the sum as a (4 * k) + 4 terms, a (4 * k), a (4 * K) is even and among the 4 terms, two are odd, so a (4 * k + 4) is even
    . rw [ha] at hm ⊢
      ring_nf at hm ⊢
      rw [add_comm]
      rw [Finset.sum_Ico_succ_top (by omega)]
      rw [show m * 4 + 4 = m * 4 + 3 + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
      rw [Finset.sum_Ico_succ_top (by omega)]
      rw [Finset.sum_Ico_succ_top (by omega)]
      conv => arg 1; equals ∑ k ∈ Ico 1 (m * 4 + 1), k ^ k + ((m * 4 + 1) ^ (m * 4 + 1) + (m * 4 + 3) ^ (m * 4 + 3) + (m * 4 + 2) ^ (m * 4 + 2) + (m * 4 + 4) ^ (m * 4 + 4)) => ring
      apply Even.add hm
      have h1 : Odd ((m * 4 + 1) ^ (m * 4 + 1)) := by
        apply Odd.pow
        rw [Nat.odd_iff, Nat.add_mod, Nat.mul_mod]
        norm_num
      have h2 : Even ((m * 4 + 2) ^ (m * 4 + 2)) := by
        rw [Nat.even_pow' (by omega)]
        rw [Nat.even_iff, Nat.add_mod, Nat.mul_mod]
        norm_num
      have h3 : Odd ((m * 4 + 3) ^ (m * 4 + 3)) := by
        apply Odd.pow
        rw [Nat.odd_iff, Nat.add_mod, Nat.mul_mod]
        norm_num
      have h4 : Even ((m * 4 + 4) ^ (m * 4 + 4)) := by
        rw [Nat.even_pow' (by omega)]
        rw [Nat.even_iff, Nat.add_mod, Nat.mul_mod]
        norm_num
      refine Even.add ?_ h4
      refine Even.add ?_ h2
      apply h1.add_odd h3
  -- now a (4 * n + 4) is not 1, even, greater than 2 so not prime and obviously n ≤ 4 * n + 4
  and_intros
  . omega
  . assumption
  . by_contra hp
    rw [Nat.Prime.even_iff hp, ha, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
    ring_nf at h
    suffices 0 ≤ ∑ x ∈ Ico 3 (4 + n * 4).succ, x ^ x by linarith
    apply Finset.sum_nonneg
    rintro i hi
    simp
  . by_contra h'
    rw [h'] at h
    simp at h