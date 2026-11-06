import Mathlib

open Real Finset

/- Task B-3.3. (20 points) Calculate the sum
$$
\frac{\sin 1}{\cos 0 \cdot \cos 1}+\frac{\sin 1}{\cos 1 \cdot \cos 2}+\frac{\sin 1}{\cos 2 \cdot \cos 3}+\ldots+\frac{\sin 1}{\cos 2008 \cdot \cos 2009}
$$
 -/
theorem algebra_220165 : ∑ i : ℕ in range 2009, sin 1 / (cos i * cos (i + 1)) = tan 2009 := calc
  -- We have sin 1 = sin (i + 1 - i).
  ∑ i : ℕ in range 2009, sin 1 / (cos i * cos (i + 1)) = ∑ i : ℕ in range 2009, sin (i + 1 - i) / (cos i * cos (i + 1)) := by
      simp only [add_sub_cancel_left]
  -- sin ((i + 1) - i) = cos i * sin (i + 1) - sin i * cos (i + 1).
  _ = ∑ i : ℕ in range 2009, (cos i * sin (i + 1) - sin i * cos (i + 1)) / (cos i * cos (i + 1)) := by
      apply sum_congr rfl
      intro i hi
      rw [sin_sub, mul_comm _ (sin i), mul_comm]
  -- (cos i * sin (i + 1) - sin i * cos (i + 1)) / (cos i * cos (i + 1))
  --    = sin (i + 1) / cos (i + 1) - sin i / cos i
  --    = tan (i + 1) - tan i.
  _ = ∑ i : ℕ in range 2009, (tan (i + 1) - tan i) := by
      apply sum_congr rfl
      intro i hi
      -- In order to prove the above equality, we need to show that cos j ≠ 0 for all integer j.
      have hcos0 (j : ℕ) : cos j ≠ 0 := by
        -- We have cos j = 0 ↔ j = (2 * k + 1) * π / 2 for some integer k.
        simp [Real.cos_eq_zero_iff]
        intro k h
        -- j is rational. Show that (2 * k + 1) * π / 2 is irrational.
        apply_fun Irrational at h
        simp at h
        apply h
        rw [show (2 * k + 1) * π / 2 = ((2 * k + 1) / 2 : ℚ) * π by simp; ring]
        -- π is irrational. It is left to show that 0 ≠ (2 * k + 1) / 2 ∈ ℚ
        apply Irrational.rat_mul irrational_pi
        simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
        clear * -
        norm_cast
        omega
      have h1 := hcos0 (i + 1)
      push_cast at h1
      rw [sub_div, mul_div_mul_left _ _ (hcos0 i), mul_div_mul_right _ _ h1]
      simp_rw [tan_eq_sin_div_cos]
  _ = tan 2009 := by
      simp_rw [show ∀ i : ℕ, (i : ℝ) + 1 = (i + 1 : ℕ) by simp]
      -- Cancel terms in the sum and get tan 2009 - tan 0 = tan 2009 - 0 = tan 2009.
      rw [sum_range_sub (fun i : ℕ => tan i) 2009]
      simp only [Nat.cast_ofNat, CharP.cast_eq_zero, tan_zero, sub_zero]