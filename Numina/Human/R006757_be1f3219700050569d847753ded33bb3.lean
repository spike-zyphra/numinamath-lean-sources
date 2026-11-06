import Mathlib

open Nat

lemma lemma1 {a k : ℕ} (h₁ : 0 < a) (h₂ : 0 < k)  : (Nat.digits 10 (10 ^ k * a + 1)).sum = (Nat.digits 10 a).sum + 1 := by
  have h₁ : 10 ≤ 10 ^ k := by exact Nat.le_self_pow (by omega) 10
  have : (10 ^ k * a) % 10 = 0 := by
    rw [Nat.mul_mod, Nat.pow_mod]
    simp only [mod_self, mul_mod_mod, mod_mul_mod, one_mod, mod_add_mod]
    have : 0 ^ k = 0 := by
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      omega
    rw [this]
    omega
  rw [digits_eq_cons_digits_div (by linarith) (by omega), List.sum_cons]
  rw [Nat.add_mod, this, add_comm, add_left_inj]
  have : (10 ^ k * a + 1) / 10 = 10 ^ (k - 1) * a := by
    rw [Nat.add_div (by omega)]
    simp only [reduceDiv, add_zero, one_mod, reduceLeDiff, this, if_false]
    have : 10 ^ k / 10 = 10 ^ (k - 1) := by
      nth_rw 1 [show k = k - 1 + 1 by omega, pow_succ]
      omega
    rw [mul_comm, Nat.mul_div_assoc, this, mul_comm]
    exact dvd_pow_self 10 (by omega)
  rw [this, Nat.digits_base_pow_mul]
  simp only [reduceLeDiff, List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, zero_add]
  all_goals linarith

lemma lemma2 : ∀k > 0, Nat.ofDigits 10 (8 :: (List.replicate (k - 1) 9)) = 10^k - 2 := by
  intro k hk
  induction' k using Nat.strongRec with k ih
  by_cases hk₁ : k = 1
  · rw [hk₁]
    norm_num
  specialize ih (k - 1) (by omega) (by omega)
  rw [Nat.ofDigits_cons] at ih
  rw [Nat.ofDigits_cons, show k - 1 = k - 1 - 1 + 1 by omega, List.replicate_succ, Nat.ofDigits_cons, show 10 * ofDigits 10 (List.replicate (k - 1 - 1) 9) = 10 ^ (k - 1) - 10 by omega]
  ring_nf
  rw [Nat.sub_mul, ←pow_succ, show k - 1 + 1 = k by omega, ←Nat.add_sub_assoc]
  omega
  rw [←pow_two, Nat.pow_le_pow_iff_right]
  all_goals omega

/-Let $k$ be a positive integer. Let $A$ be the $k$-digit number, all of whose digits are 9 (for example, if $k=3$, $A=999$). What is the sum of the digits of $A^2$? Show that this sum is $9k$.-/
theorem number_theory_640843 (k : ℕ) (hk : 0 < k) (A : ℕ) (hA : A = ∑ i ∈ Finset.range k, 9 * 10^i) : (Nat.digits 10 (A^2)).sum = 9 * k := by
  have hA₁ : A = 10^k - 1 := by
    rw [hA]
    generalize k = a
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega
  have hk₁ : 10 ≤ 10 ^ k := by exact Nat.le_self_pow (by omega) 10
  have hA₂ : A^2 = 10 ^ k * (10 ^ k - 2) + 1 := by
    rw [hA₁]
    set n := 10 ^ k with hn
    rw [pow_two, Nat.mul_sub, mul_one, Nat.sub_mul, one_mul, Nat.mul_sub]
    have : 2 * n < n * n := by
      apply Nat.mul_lt_mul_of_pos_right
      all_goals omega
    rw [Nat.sub_sub, Nat.sub_eq_iff_eq_add, Nat.add_assoc]
    rw [show 1 + (n + (n - 1)) = n * 2 by omega, Nat.sub_add_cancel]
    all_goals omega

  rw [hA₂, lemma1 (by omega) (by linarith), ←lemma2 _ (by omega)]
  rw [Nat.digits_ofDigits _ (by simp) _ (by simp)]
  simp only [List.sum_cons, List.sum_replicate, smul_eq_mul, reduceLeDiff, zero_lt_one, digits_of_two_le_of_pos, one_mod, reduceDiv, digits_zero, List.sum_nil, add_zero]
  · omega
  · intro h₁
    rw [List.getLast_eq_getLastD, List.getLastD_eq_getLast?, List.getLast?_replicate]
    split_ifs
    · simp
    · simp
