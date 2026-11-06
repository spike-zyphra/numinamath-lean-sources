import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-We need the following lemma on the summation of cubics-/
lemma lm_8962 : ∑ k_1 ∈ Finset.Icc 1 2016, k_1 ^ 3 = 1008 ^ 2 * 2017 ^ 2 := by
  have (t : ℕ) : ∑ k_1 ∈ Finset.Icc 1 t, k_1 ^ 3 = (t * (t+1) / 2) ^ 2 := by
    induction t with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top, ih]; rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
      · rw [hk]; ring_nf
        have h1 : (k * 2 + k ^ 2 * 4) / 2 = k + k ^ 2 * 2 := by
          rw [Nat.div_eq_iff_eq_mul_left]; ring; linarith; use k+k^2*2; ring
        have h2 : (2 + k * 6 + k ^ 2 * 4) / 2 = 1 + k * 3 + k ^ 2 * 2 := by
          rw [Nat.div_eq_iff_eq_mul_left]; ring; linarith; use 1+k*3+k^2*2; ring
        rw [h1, h2]; ring
      rw [hk]; ring_nf
      have t3 : (2 + k * 6 + k ^ 2 * 4) / 2 = 1 + k * 3 + k ^ 2 * 2 := by
        rw [Nat.div_eq_iff_eq_mul_left]; ring; linarith; use 1+k*3+k^2*2; ring
      have t4 : (6 + k * 10 + k ^ 2 * 4) / 2 = 3 + k * 5 + k ^ 2 * 2 := by
        rw [Nat.div_eq_iff_eq_mul_left]; ring; linarith; use 3+k*5+k^2*2; ring
      rw [t3, t4]; ring; linarith
  have sum2016 := this 2016
  rw [sum2016]; norm_num

/-Prove that there exist infinitely many integers \(n\) which satisfy \(2017^2 | 1^n + 2^n + ... + 2017^n\).-/
theorem number_theory_8962_1 (k : ℕ):
2017^2 ∣ ∑ i in Finset.Icc 1 2017, i ^ (k * ((2017 ^ 2).totient) + 3) := by
-- Apply the Fermat-Euler totient theorem to get a key division relation
  have r1 : ∀ i, i ∈ Finset.Icc 1 2016 →
  2017 ^ 2 ∣ i ^ (k * ((2017 ^ 2).totient) + 3) - i ^ 3 := by
    intro i hi; simp at hi; rcases hi with ⟨hil, hir⟩
    rw [pow_add]; nth_rw 2 [mul_comm]; rw [pow_mul]
-- Since $2017$ is a prime number, any $i$ less than $2017$ is coprime to $2017$ and its powers
    have u1 : Coprime (2017^2) i := by
      rw [Nat.coprime_pow_left_iff]; apply Nat.coprime_of_lt_prime
      linarith; linarith; norm_num; norm_num
-- Apply the Fermat-Euler totient theorem to get a congruence relation
    have u2 := Nat.ModEq.pow_totient (Nat.coprime_comm.mp u1)
    apply Nat.ModEq.pow k at u2; rw [one_pow] at u2
-- Rewrite the congruence relation to a division relation, then unwrap the defition of division
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd'] at u2
    rcases u2 with ⟨t, ht⟩; use t * i ^ 3
    rw [← mul_assoc, ← ht, ← pow_mul, Nat.sub_mul, one_mul]
    apply Nat.one_le_pow; apply pow_pos; linarith
-- Split the summation, isolating the last term which is obviously divisible by $2017^2$
  rw [Finset.sum_Icc_succ_top, show 2016+1=2017 by norm_num]
  apply Nat.dvd_add
-- Split the sum of the first $2016$ terms
  · have t1 : ∑ k_1 ∈ Finset.Icc 1 2016, k_1 ^ (k * φ (2017 ^ 2) + 3) =
    ∑ k_1 ∈ Finset.Icc 1 2016, (k_1 ^ (k * φ (2017 ^ 2) + 3) - k_1 ^ 3) + ∑ k_1 ∈ Finset.Icc 1 2016, k_1 ^ 3 := by
      rw [← Finset.sum_add_distrib]; congr; ext x
      by_cases h'x : x ≤ 0
      · simp at h'x; rw [h'x]; simp
      push_neg at h'x; rw [Nat.sub_add_cancel]
      apply Nat.pow_le_pow_right; linarith; simp
    rw [t1]; apply Nat.dvd_add
-- Apply r1 to prove that the first sum is divisible by $2017^2$
    · apply Finset.dvd_sum; assumption
-- Apply lemma lm1 to prove that the second sum is divisible by $2017^2$
    use 1008^2; rw [mul_comm]; exact lm_8962
  apply Nat.pow_dvd_pow; simp; norm_num

/-Prove that there are infinitely many such integers-/
theorem number_theory_8962_2 : Set.Infinite {n : ℕ | 2017^2 ∣ ∑ i in Finset.Icc 1 2017, i^n} := by
  let f (k : ℕ) : ℕ := k * ((2017 ^ 2).totient) + 3
  have h2 : Function.Injective f := by
    intro x1 x2 h12; simp [f] at h12; assumption
  apply Set.infinite_of_injective_forall_mem h2; intro x;
  simp only [f, Set.mem_setOf_eq]; exact number_theory_8962_1 x
