import Mathlib

open Real Set
open scoped Real

/- * Given $\sin ^{2} A+\sin ^{2} B+\sin ^{2} C=1$, where $A, B, C$ are all acute angles, prove:

$$

\frac{\pi}{2} \leqslant A+B+C \leqslant \pi .

$$
 -/
theorem inequalities_113230 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (h : sin A ^ 2 + sin B ^ 2 + sin C ^ 2 = 1) :
    π / 2 ≤ A + B + C ∧ A + B + C ≤ π := by
  -- Use the condition to derive a expression for sin A ^ 2
  have sin_a_sq : sin A ^ 2 = cos (B + C) * cos (B - C) := by
    calc
      -- Use the condition
      sin A ^ 2 = 1 - sin B ^ 2 - sin C ^ 2 := by linarith
      _ = cos B ^ 2 - sin C ^ 2 := by simp [cos_sq']
      _ = sin (π / 2 - B) ^ 2 - sin C ^ 2 := by simp [sin_pi_div_two_sub]
      -- Factor difference of squares
      _ = (sin (π / 2 - B) - sin C) * (sin (π / 2 - B) + sin C) := by ring
      -- Use sin subtraction formula
      _ = _ * (sin (π / 2 - B) + sin C) := by rw [sin_sub_sin]
      _ = 2 * sin ((π / 2 - B - C) / 2) * cos ((π / 2 - B + C) / 2) * (sin (π / 2 - B) - sin (-C)) := by simp [sin_neg]
      _ = 2 * sin ((π / 2 - B - C) / 2) * cos ((π / 2 - B + C) / 2) * (2 * sin ((π / 2 - B + C) / 2) * cos ((π / 2 - B - C) / 2)) := by rw [sin_sub_sin, sub_neg_eq_add, sub_eq_add_neg]
      _ = (2 * sin ((π / 2 - B - C) / 2) * cos ((π / 2 - B - C) / 2)) * (2 * sin ((π / 2 - B + C) / 2) * cos ((π / 2 - B + C) / 2)) := by linarith
      -- Use sin double angle formula
      _ = sin (π / 2 - (B + C)) * sin (π / 2 - (B - C)) := by rw [← sin_two_mul, ← sin_two_mul, mul_div_cancel₀ _ (by positivity), mul_div_cancel₀ _ (by positivity), sub_add, sub_sub]
      -- Turn into cos
      _ = cos (B + C) * cos (B - C) := by repeat rw [sin_pi_div_two_sub]
  have cos_pos : 0 < cos (B + C) := by
    -- Show that product is zero
    have prod_pos : 0 < cos (B + C) * cos (B - C) := by
      -- Rewrite as sin A ^ 2
      rw [← sin_a_sq]
      have : 0 < sin A := by
        apply sin_pos_of_mem_Ioo
        simp
        simp at hA
        exact ⟨by linarith, by linarith⟩
      nlinarith
    -- Show that cos (B - C) is nonnegative
    have cos_diff_pos : 0 < cos (B - C) := by
      have : B - C ∈ Ioo (-(π / 2)) (π / 2) := by simp at hA hB hC; simp; exact ⟨by linarith, by linarith⟩
      exact cos_pos_of_mem_Ioo this
    exact (mul_pos_iff_of_pos_right (cos_diff_pos)).mp prod_pos
  -- Show that B + C is acute
  have b_add_c_small : B + C ≤ π / 2 := by
    have cos_mem_Ioo : 0 < B + C ∧ B + C < π := by
      simp at hB hC
      exact ⟨by linarith, by linarith⟩
    -- Prove by contraposition
    contrapose cos_pos
    simp
    simp at cos_pos
    apply cos_nonpos_of_pi_div_two_le_of_le <;> linarith
  -- We are able to prove the upper bound now
  refine ⟨?_, by simp at hA; linarith⟩
  -- Now we show that cos (B - C) ≥ cos (B + C)
  have cos_le_cos : cos (B + C) ≤ cos (B - C) := by
    have : B ≤ C ∨ C ≤ B := le_total _ _
    -- Do case work on whether B or C is smaller
    rcases this with B_small | C_small
    · rw [← cos_neg (B - C), neg_sub]
      apply cos_le_cos_of_nonneg_of_le_pi (by linarith)
      · trans π / 2 <;> linarith [pi_pos]
      simp at hB
      linarith
    apply cos_le_cos_of_nonneg_of_le_pi (by linarith)
    · trans π / 2 <;> linarith [pi_pos]
    simp at hC
    linarith
  -- Have a sin inequality
  have : sin A ^ 2 ≥ sin (π / 2 - B - C) ^ 2 := by
    calc
      sin A ^ 2 = cos (B + C) * cos (B - C) := by tauto
      _ ≥ cos (B + C) ^ 2 := by rw [pow_two, ge_iff_le, mul_le_mul_left cos_pos]; tauto
      _ = sin (π / 2 - B - C) ^ 2 := by rw [← sin_pi_div_two_sub]; rw [sub_sub]
  -- Remove the squares from both sides
  have : sin A ≥ sin (π / 2 - B - C) := by
    have sin_nonneg : 0 ≤ sin A := by simp at hA; apply sin_nonneg_of_mem_Icc; simp; exact ⟨by linarith, by linarith⟩
    have sin_nonneg' : 0 ≤ sin (π / 2 - B - C) := by apply sin_nonneg_of_mem_Icc; simp; simp at hB hC; exact ⟨by linarith, by linarith⟩
    rw [ge_iff_le]
    apply (sq_le_sq₀ sin_nonneg' sin_nonneg).mp
    linarith
  -- Remove sin from both sides
  have A_ge : A ≥ π / 2 - B - C := by
    contrapose this
    simp
    simp at this
    have : A < π / 2 - B - C := by linarith
    apply sin_lt_sin_of_lt_of_le_pi_div_two
    · simp at hA; linarith
    · simp at hB hC; linarith
    tauto
  -- Conclude
  linarith