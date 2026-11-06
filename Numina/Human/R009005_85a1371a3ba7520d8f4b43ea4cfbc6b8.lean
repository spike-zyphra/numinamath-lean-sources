import Mathlib

open Complex

/- 9. (16 points) Let the complex number $z=\cos \frac{2 \pi}{13}+\mathrm{i} \sin \frac{2 \pi}{13}$. Find the value of $\left(z^{-12}+z^{-11}+z^{-10}\right)\left(z^{3}+1\right)\left(z^{6}+1\right)$. -/
theorem algebra_271604 {z : ℂ} (hz : z = exp (I * 2 * Real.pi / 13)) :
    (z⁻¹ ^ 12 + z⁻¹ ^ 11 + z⁻¹ ^ 10) * (z^3 + 1) * (z^6 + 1) = -1 := by
  -- we know that z is a primitive 13th root of unity
  have hzr: IsPrimitiveRoot z 13 := by
    apply (Complex.isPrimitiveRoot_iff z 13 (by norm_num)).mpr;
    use 1; exact ⟨by norm_num, by simp [hz]; apply congr_arg; ring_nf⟩;

  -- let's compute z^13
  have hz13 : z^13 = 1 := by
    rw [hz, ← exp_nat_mul, mul_comm, div_mul]; rify; rw [div_self (by norm_num), div_one];
    refine exp_eq_one_iff.mpr ?_; use 1; simp; ring_nf;

  -- we can also compute z^12 + z^11 + ... + z  = -1
  have hzsum: z^12 + z^11 + z^10 + z^9 + z^8 + z^7 + z^6 + z^5 + z^4 + z^3 + z^2 + z = -1 := by
    have h:= IsPrimitiveRoot.geom_sum_eq_zero hzr (by norm_num);
    repeat rw [Finset.sum_range_succ] at h
    simp at h; ring_nf at h ⊢; apply congr_arg (fun x => -1 +x) at h; ring_nf at h; assumption
  -- to work on the goal we need a few mini lemmas
  have hzinv1: z⁻¹ = z^12 := by
    apply congr_arg (fun x => x * z⁻¹) at hz13; simp at hz13; rw [hz13.symm];
    refine (mul_inv_eq_iff_eq_mul₀ (by exact IsPrimitiveRoot.ne_zero hzr (by norm_num))).mpr rfl
  -- now let's work on the goal
  calc (z⁻¹ ^ 12 + z⁻¹ ^ 11 + z⁻¹ ^ 10) * (z ^ 3 + 1) * (z ^ 6 + 1)
  _ = ((z ^ 12) ^ 12 + (z ^ 12) ^ 11 + (z ^ 12) ^ 10) * (z ^ 3 + 1) * (z ^ 6 + 1) := by rw [hzinv1]
  _ = (z ^ 120 + z ^ 132 + z ^ 144) * (z ^ 3 + 1) * (z ^ 6 + 1) := by simp; left; left; ring_nf;
  _ = (z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z^3 + z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 2 + z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z ^ 13 * z) * (z ^ 3 + 1) * (z ^ 6 + 1) := by ring_nf
  _ = (z ^ 1 + z ^ 2 + z ^ 3) * (z ^ 3 + 1) * (z ^ 6 + 1) := by rw [hz13]; ring_nf
  _ = z^12 + z^11 + z^10 + z^9 + z^8 + z^7 + z^6 + z^5 + z^4 + z^3 + z^2 + z := by ring_nf
  _ = -1 := by rw [hzsum]