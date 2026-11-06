import Mathlib.Tactic
import Mathlib.Util.Delaborators

/- Set A consists of m consecutive integers whose sum is 2m, and set B consists of 2m consecutive integers whose sum is m. The absolute value of the difference between the greatest element of A and the greatest element of B is 99. Find m. -/

theorem AIME_Algebra_724 (A B : Finset ℤ) (a b : ℤ) (m : ℕ) (mpos : m > 0)
    (ha : A = Finset.Icc a (a+m-1)) (sum_a : A.sum (fun x ↦ x) = 2*m)
    (hb : B = Finset.Icc b (b+2*m-1)) (sum_b : B.sum (fun x ↦ x) = m)
    (d : |(a+m-1) - (b+2*m-1)| = 99) : m = 201 := by
  -- We need this to cast the sums
  have cast_sum (n : ℕ) : Finset.sum (Finset.range n) (fun x ↦ (x : ℤ))
      = Finset.sum (Finset.range n) (fun x ↦ x) := by simp
  -- First we rewrite the proposition about the difference
  apply congrArg (HMul.hMul 2) at d
  rw [← abs_two, ← abs_mul] at d
  simp only [Nat.abs_ofNat, sub_sub_sub_cancel_right, Int.reduceMul] at d
  -- We compute the sum of the elements of A
  have sum_a' : A.sum (fun x ↦ x) = (m * a + Nat.choose m 2) := by
    simp [ha, Int.Icc_eq_finset_map, Finset.sum_add_distrib, cast_sum, Finset.sum_range_id,
      Nat.choose_two_right]
  -- We compute the sum of the elements of B
  have sum_b' : B.sum (fun x ↦ x) = 2 * m * b + m * (2*m-1) := by
    simp only [hb, Int.Icc_eq_finset_map, sub_add_cancel, add_sub_cancel_left, Finset.sum_map,
      Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.ofNat_pos,
      mul_nonneg_iff_of_pos_left, Nat.cast_nonneg, Int.toNat_of_nonneg, cast_sum,
      Finset.sum_range_id, Int.ofNat_ediv, Nat.cast_mul, Nat.cast_ofNat, add_right_inj]
    rw [mul_assoc, mul_comm, EuclideanDomain.mul_div_assoc]
    · simp [Int.toNat_pred_coe_of_pos, mpos]
    · rfl
  -- We compute the value of a
  have val_a : 2*a = 4 - (m-1) := by
    rw [sum_a] at sum_a'
    apply congrArg (HMul.hMul 2) at sum_a'
    rw [mul_add, Nat.choose_two_right] at sum_a'
    rw_mod_cast [Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _)] at sum_a'
    ring_nf at sum_a'
    rw [(Nat.cast_mul m _), (Nat.cast_mul m _), mul_assoc, ← mul_add] at sum_a'
    apply mul_left_cancel₀ (by linarith) at sum_a'
    rw_mod_cast [sum_a']
    ring_nf
    rw [self_eq_add_right]
    apply Int.sub_eq_zero.mpr
    exact Eq.symm (Int.subNatNat_of_le mpos)
  -- We compute the value of b
  have val_b : 2*b = 2 - 2*m := by
    rw [sum_b] at sum_b'
    rw [mul_assoc, mul_comm, mul_assoc, ← mul_add] at sum_b'
    nth_rewrite 1 [← mul_one m, (Nat.cast_mul m 1)] at sum_b'
    apply mul_left_cancel₀  (by linarith) at sum_b'
    rw [Nat.cast_one] at sum_b'
    nth_rw 2 [← one_add_one_eq_two, sum_b']
    ring
  -- We substitute the values of a and b and complete the computation
  rw [mul_sub, mul_add, mul_add, val_a, val_b, abs_eq (by linarith)] at d
  rcases d with h | h
  · linarith
  · linarith