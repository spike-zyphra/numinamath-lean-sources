import Mathlib

/-Given that  ${a_n}$  and  ${b_n}$  are two sequences of integers defined by
\begin{align*}
a_1=1, a_2=10, a_{n+1}=2a_n+3a_{n-1} & ~~~\text{for }n=2,3,4,\ldots,
b_1=1, b_2=8, b_{n+1}=3b_n+4b_{n-1} & ~~~\text{for }n=2,3,4,\ldots.
\end{align*}

Prove that, besides the number  $1$ , no two numbers in the sequences are identical.-/
theorem number_theory_8543 (a b : ℕ → ℤ)
(ha0 : a 0 = 1) (ha1 : a 1 = 10)
(ha : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n)
(hb0 : b 0 = 1) (hb1 : b 1 = 8)
(hb : ∀ n, b (n + 2) = 3 * b (n + 1) + 4 * b n) :
(∀ m n, m ≠ n → a m ≠ a n ∧ b m ≠ b n) ∧
∀ m n, ¬ (m = 0 ∧ n = 0) → a m ≠ b n := by
-- Prove that the two sequences are positive by strong induction
  have apos : ∀ n, 0 < a n := by
    intro n; apply Nat.case_strong_induction_on n
    · rw [ha0]; norm_num
    intro k hk; by_cases h' : k ≤ 1
    · interval_cases k; simp_all; simp_all
    push_neg at h'
    have r1 := ha (k - 1)
    have : k - 1 + 2 = k + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this] at r1
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r1
    rw [r1]; apply Int.add_pos; simp; apply hk; rfl
    simp; apply hk; simp

  have bpos : ∀ n, 0 < b n := by
    intro n; apply Nat.case_strong_induction_on n
    · rw [hb0]; norm_num
    intro k hk; by_cases h' : k ≤ 1
    · interval_cases k; simp_all; simp_all
    push_neg at h'
    have r1 := hb (k - 1)
    have : k - 1 + 2 = k + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this] at r1
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r1
    rw [r1]; apply Int.add_pos; simp; apply hk; rfl
    simp; apply hk; simp

-- Prove that the two sequences are strictly increasing
  have amono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n; by_cases h' : n ≤ 1
    · interval_cases n; simp_all; simp_all
    push_neg at h'
    have r1 := ha (n-1)
    have : n - 1 + 2 = n + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this, show n-1+1=n by rw [Nat.sub_add_cancel]; linarith] at r1
    rw [r1]; linarith [apos n, apos (n-1)]

  have bmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro n; by_cases h' : n ≤ 1
    · interval_cases n; simp_all; simp_all
    push_neg at h'
    have r1 := hb (n-1)
    have : n - 1 + 2 = n + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this, show n-1+1=n by rw [Nat.sub_add_cancel]; linarith] at r1
    rw [r1]; linarith [bpos n, bpos (n-1)]

-- Prove the first two claims
  have aneq : ∀ m n, m ≠ n → a m ≠ a n := by
    intro m n hmn
    · cases lt_or_gt_of_ne hmn with
    | inl h => have := amono h; linarith
    | inr h => rw [gt_iff_lt] at h; have := amono h; linarith
  have bneq : ∀ m n, m ≠ n → b m ≠ b n := by
    intro m n hmn
    · cases lt_or_gt_of_ne hmn with
    | inl h => have := bmono h; linarith
    | inr h => rw [gt_iff_lt] at h; have := bmono h; linarith

-- To prove the last claim, we need formula of closed form for the two sequences
  have acf : ∀ n, 60 * a n = 55 * 3 ^ (n + 1) + 105 * (-1) ^ (n + 1) := by
    intro n; apply Nat.case_strong_induction_on n; simp_all
    intro k hk; by_cases h'k : k < 1; simp_all; push_neg at h'k
    have r1 := ha (k-1)
    have : k - 1 + 2 = k + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this] at r1
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r1
    have r2 := hk k (show k≤k by rfl)
    have r3 := hk (k-1) (show k-1≤k by simp)
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r3
    rw [show k+1+1=k+2 by simp, r1, mul_add]
    nth_rw 2 [mul_comm]; rw [← mul_assoc]; nth_rw 4 [mul_comm]; rw [← mul_assoc]
    rw [r2, r3]; ring

  have bcf : ∀ n, 60 * b n = 27 * 4 ^ (n + 1) + 48 * (-1) ^ (n + 1) := by
    intro n; apply Nat.case_strong_induction_on n; simp_all
    intro k hk; by_cases h'k : k < 1; simp_all; push_neg at h'k
    have r1 := hb (k-1)
    have : k - 1 + 2 = k + 1 := by
      rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
      norm_num; linarith
    rw [this] at r1
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r1
    have r2 := hk k (show k≤k by rfl)
    have r3 := hk (k-1) (show k-1≤k by simp)
    rw [show k-1+1=k by rw [Nat.sub_add_cancel]; linarith] at r3
    rw [show k+1+1=k+2 by simp, r1, mul_add]
    nth_rw 2 [mul_comm]; rw [← mul_assoc]; nth_rw 4 [mul_comm]; rw [← mul_assoc]
    rw [r2, r3]; ring

-- Prove the final result by modulo $27$
  constructor
  · intro m n hmn; exact ⟨aneq m n hmn, bneq m n hmn⟩
  intro m n hmn; by_contra h'
  rw [← Int.mul_eq_mul_left_iff (show (60:ℤ)≠0 by simp)] at h'
  rw [acf m, bcf n] at h'
-- Assume that $m$ is greater or equal to $2$
  by_cases hm : 2 ≤ m
  · have r1 : (55 * 3 ^ (m + 1) + 105 * (-1) ^ (m + 1)) % 27 =
    (27 * 4 ^ (n + 1) + 48 * (-1) ^ (n + 1)) % 27 := by rw [h']
    have : (3:ℤ) ^ (m + 1) = 27 * 3 ^ (m - 2) := by
      rw [show (27:ℤ)=3^3 by simp, ← pow_add]; simp
      rw [show 3=1+2 by simp, add_assoc, Nat.add_sub_cancel', add_comm]; assumption
    rw [this, ← mul_assoc] at r1; nth_rw 2 [mul_comm] at r1
    rw [mul_assoc, ← Int.emod_add_emod] at r1
    nth_rw 2 [← mul_one (27:ℤ)] at r1
    rw [Int.mul_emod_mul_of_pos] at r1; simp at r1
    rw [← Int.emod_add_emod] at r1; nth_rw 3 [← mul_one (27:ℤ)] at r1
    rw [Int.mul_emod_mul_of_pos] at r1; simp at r1
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero] at r1
-- In order to compute the power of $-1$, we split the proof to $4$ cases
    cases Nat.even_or_odd (m+1) with
    | inl hl =>
      cases Nat.even_or_odd (n+1) with
      | inl hll =>
        rw [Even.neg_one_pow hl, Even.neg_one_pow hll] at r1
        simp at r1; contradiction
      | inr hrr =>
        rw [Even.neg_one_pow hl, Odd.neg_one_pow hrr] at r1
        simp at r1; contradiction
    | inr hr =>
          cases Nat.even_or_odd (n+1) with
      | inl hll =>
        rw [Odd.neg_one_pow hr, Even.neg_one_pow hll] at r1
        simp at r1; contradiction
      | inr hrr =>
        rw [Odd.neg_one_pow hr, Odd.neg_one_pow hrr] at r1
        simp at r1; contradiction
    norm_num; norm_num
-- Check $m=0$ is impossible
  push_neg at hm; interval_cases m; simp at hmn
  simp_all; push_neg at hmn
  rw [← Nat.pos_iff_ne_zero, Nat.lt_iff_add_one_le] at hmn; simp at hmn
  cases Nat.even_or_odd (n+1) with
  | inl hl =>
    rw [Even.neg_one_pow hl, mul_one, ← @sub_left_inj _ _ 48] at h'
    rw [Int.add_sub_cancel] at h'; simp at h'
    have : (0:ℤ) < 4 ^ (n + 1) := by apply pow_pos; norm_num
    linarith
  | inr hr =>
    rw [Odd.neg_one_pow hr, mul_neg_one, ← sub_eq_add_neg] at h'
    rw [← Int.add_right_inj 48] at h'; simp at h'
    have : (4:ℤ) ^ 2 ≤ 4 ^ (n + 1) := by
      rw [pow_le_pow_iff_right]; simp; assumption; norm_num
    linarith
-- Check $m=1$ is impossible
  simp_all; cases Nat.even_or_odd (n+1) with
  | inl hl =>
    rw [Even.neg_one_pow hl, mul_one, ← @sub_left_inj _ _ 48] at h'
    rw [Int.add_sub_cancel] at h'; simp at h'
    have : (23:ℤ) ∣ 27 * 4 ^ (n + 1) := by rw [← h']; norm_num
    apply Prime.dvd_or_dvd at this; rcases this; contradiction
    rename_i d23; rw [Prime.dvd_pow_iff_dvd] at d23; contradiction
    rw [Int.prime_iff_natAbs_prime]; norm_num; linarith
    rw [Int.prime_iff_natAbs_prime]; norm_num
  | inr hr =>
    rw [Odd.neg_one_pow hr, mul_neg_one, ← sub_eq_add_neg] at h'
    rw [← Int.add_right_inj 48] at h'; simp at h'
    have : (27*3:ℤ) ∣ 27 * 4 ^ (n + 1) := by rw [← h']; norm_num
    apply Int.dvd_of_mul_dvd_mul_left at this
    rw [Prime.dvd_pow_iff_dvd] at this; contradiction
    rw [Int.prime_iff_natAbs_prime]; norm_num; linarith; norm_num
