import Mathlib

open Real Set

/- 3. Given real numbers $x_{1}, \ldots, x_{n}$. Find the maximum value of the expression


$$

A=\left(\sin x_{1}+\ldots+\sin x_{n}\right) \cdot\left(\cos x_{1}+\ldots+\cos x_{n}\right)

$$
 -/
theorem algebra_220000 {n : ℕ} :
    IsGreatest {a | ∃ x : Fin n → ℝ, a = (∑ i : Fin n, sin (x i)) * (∑ i : Fin n, cos (x i))} (n^2 / 2) := by
  simp only [IsGreatest, mem_setOf_eq, upperBounds, forall_exists_index, forall_eq_apply_imp_iff]
  constructor
  -- Show that there exist numbers x_i such that (∑ i : Fin n, sin (x i)) * (∑ i : Fin n, cos (x i)) = n ^ 2 / 2.
  -- Take x_i = π / 4 and get the result after simplifications.
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
  -- This follows from the inequality (∑ i : Fin n, f(i))^2 ≤ n * ∑ f(i)^2.
  have ha2 : a ^ 2 ≤ n * ∑ i : Fin n, sin (x i) ^ 2 := by
    apply le_trans sq_sum_le_card_mul_sum_sq
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  -- Show that a ^ 2 ≤ n * ∑ i : Fin n, cos (x i) ^ 2.
  -- This follows from the inequality (∑ i : Fin n, f(i))^2 ≤ n * ∑ f(i)^2.
  have hb2 : b ^ 2 ≤ n * ∑ i : Fin n, cos (x i) ^ 2 := by
    apply le_trans sq_sum_le_card_mul_sum_sq
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  -- Show that 2 * a * b ≤ n ^ 2.
  suffices 2 * a * b ≤ n ^ 2 by linarith
  calc
    -- We have 2 * a * b ≤ a ^ 2 + b ^ 2 for any a and b.
    2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_add_pow_two a b
    -- a ^ 2 + b ^ 2 ≤ n * (∑ i : Fin n, sin (x i) ^ 2 + ∑ i : Fin n, cos (x i) ^ 2).
    -- This follows from inequalities ha2 and hb2.
    _ ≤ n * (∑ i : Fin n, sin (x i) ^ 2 + ∑ i : Fin n, cos (x i) ^ 2) := by
        rw [mul_add]
        gcongr
    -- We get ∑ i : Fin n, sin (x i) ^ 2 + ∑ i : Fin n, cos (x i) ^ 2
    --    = ∑ i : Fin n, (sin (x i) ^ 2 + cos (x i) ^ 2) = ∑ i : Fin n, 1.
    _ = n * ∑ i : Fin n, 1 := by
        congr
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intros
        simp only [sin_sq_add_cos_sq]
    -- We conclude that 2 * a * b ≤ n * ∑ i : Fin n, 1 = n * n = n ^ 2.
    _ = n ^ 2 := by simp [pow_two]