import Mathlib

/-Define the sequnce   ${(a_n)}_{n\ge1}$  by  $a_1=1$  and  $a_n=5a_{n-1}+3^{n-1}$  for  $n\ge2$ .
Find the greatest power of  $2$  that divides  $a_{2^{2019}}$ .-/
theorem number_theory_8959 (a : ℕ → ℚ) (h1 : a 1 = 1)
(ha : ∀ n, 1 ≤ n → a (n + 1) = 5 * a n + 3 ^ n) :
∃ t : ℕ, a (2^2019) = t ∧ padicValNat 2 t = 2021 := by
-- Use induction on $n$ to prove that $a(n)$ equals $1/2(5^n-3^n)$
  have h'a : ∀ n, 1 ≤ n → a n = (1/2) * (5 ^ n - 3 ^ n) := by
    intro k hk; induction k with
    | zero => simp_all
    | succ k ih =>
      by_cases h'k : k = 0; simp_all; field_simp; norm_num
      push_neg at h'k; rw [Nat.ne_zero_iff_zero_lt, Nat.lt_iff_add_one_le] at h'k
      simp at h'k; replace ih := ih h'k
      have hk1 := ha k h'k
      rw [ih] at hk1; rw [hk1]; field_simp; ring
-- Show that $5^2^t-3^2^t$ is even by showing each power is odd and odd minus odd is even
  have d2 : ∀ t, 2 ∣ 5 ^ 2 ^ t - 3 ^ 2 ^ t := by
    intro t
    have : Even (5 ^ 2 ^ t - 3 ^ 2 ^ t) := by
      rw [Nat.even_sub', ← Int.odd_coe_nat, ← Int.odd_coe_nat]
      push_cast; rw [Int.odd_pow, Int.odd_pow]; simp
      constructor
      · intro; use 1; norm_num
      intro; use 2; norm_num; rw [Nat.pow_le_pow_iff_left]; norm_num
      rw [Nat.ne_zero_iff_zero_lt]; apply Nat.pow_pos; norm_num
    rw [← even_iff_two_dvd]; assumption
-- Prove a general version of the final result by using the key lemma padicValNat.pow_two_sub_pow
-- which computes the greatest power of $2$ dividing a subtraction of two powers
  have r2 : ∀ k, 1 ≤ k → ∃ t : ℕ, a (2 ^ k) = t ∧ padicValNat 2 t = k + 2 := by
    intro k h'k;
    have hk := h'a (2 ^ k) (show 1≤2^k by apply Nat.one_le_pow; norm_num)
    rcases d2 k with ⟨t, ht⟩; use t; constructor
    · rw [hk]; field_simp;
-- Convert types
      rw [show (t:ℚ)*2=((t*2):ℕ) by simp]
      have ct1 : (5:ℚ)^2^k-(3:ℚ)^2^k=((5^2^k-3^2^k):ℕ) := by
        rw [Nat.cast_sub]; simp
        rw [Nat.pow_le_pow_iff_left]; norm_num
        rw [Nat.ne_zero_iff_zero_lt]; apply Nat.pow_pos; norm_num
      rw [ct1, Nat.cast_inj, mul_comm]; assumption
    have : t = (5 ^ 2 ^ k - 3 ^ 2 ^ k) / 2 := by
      symm; rw [Nat.div_eq_iff_eq_mul_right]; assumption; norm_num
      apply d2
-- Apply key lemma padicValNat.pow_two_sub_pow
    rw [this, padicValNat.div]; simp; apply @Nat.add_right_cancel _ 1 _
    rw [padicValNat.pow_two_sub_pow]; simp
    rw [show 8=2^3 by norm_num, padicValNat.pow]; simp; ring
    norm_num; norm_num; norm_num; norm_num
    rw [Nat.ne_zero_iff_zero_lt]; apply Nat.pow_pos; norm_num
    use 2^(k-1); rw [← two_mul]; nth_rw 2 [show 2=2^1 by simp]
    rw [← pow_add]; simp; rw [Nat.add_sub_cancel']; assumption
    apply d2
-- Specialize to the case when $k$ is $2019$
  apply r2; norm_num