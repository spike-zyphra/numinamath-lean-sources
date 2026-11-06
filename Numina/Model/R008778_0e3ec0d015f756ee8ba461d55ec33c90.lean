import Mathlib

open Real Set

theorem algebra_220000 {n : ℕ} :
    IsGreatest {a | ∃ x : Fin n → ℝ, a = (∑ i : Fin n, sin (x i)) * (∑ i : Fin n, cos (x i))} (n^2 / 2) := by
  simp only [IsGreatest, mem_setOf_eq, upperBounds, forall_exists_index, forall_eq_apply_imp_iff]
  constructor
  -- Show that there exist numbers x_i such that (∑ i : Fin n, sin (x i)) * (∑ i : Fin n, cos (x i)) = n ^ 2 / 2.
  · use fun _ => π / 4
    simp
    ring_nf
    rw [sq_sqrt (by norm_num)]
    ring
  -- Show that (∑ i : Fin n, sin (x i)) * (∑ i : Fin n, cos (x i)) ≤ n ^ 2 / 2 for any numbers x_i.
  intro x
  -- Let a = ∑ i : Fin n, sin (x i) and b = ∑ i : Fin n, cos (x i).
  set a := ∑ i : Fin n, sin (x i)
  set b := ∑ i : Fin n, cos (x i)
  -- Show that a ^ 2 ≤ n * ∑ i : Fin n, sin (x i) ^ 2.
  have ha2 : a ^ 2 ≤ n * ∑ i : Fin n, sin (x i) ^ 2 := by
    apply le_trans sq_sum_le_card_mul_sum_sq
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  -- Show that a ^ 2 ≤ n * ∑ i : Fin n, cos (x i) ^ 2.
  have hb2 : b ^ 2 ≤ n * ∑ i : Fin n, cos (x i) ^ 2 := by
    apply le_trans sq_sum_le_card_mul_sum_sq
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  -- Show that 2 * a * b ≤ n ^ 2.
  suffices 2 * a * b ≤ (n : ℝ) ^ 2 by linarith
  calc
    2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_pow_two a b
    _ ≤ n * (∑ i : Fin n, sin (x i) ^ 2 + ∑ i : Fin n, cos (x i) ^ 2) := by
        rw [mul_add]
        gcongr
    _ = n * ∑ i : Fin n, (sin (x i) ^ 2 + cos (x i) ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ = n * ∑ i : Fin n, 1 := by
      congr
      funext i
      rw [Real.sin_sq_add_cos_sq]
    _ = n * (n : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = (n : ℝ) ^ 2 := by
      ring