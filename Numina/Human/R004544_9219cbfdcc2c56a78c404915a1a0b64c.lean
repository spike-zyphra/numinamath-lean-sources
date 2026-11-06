import Mathlib

open Real

-- sin A - cos A = √2 * sin (A - π / 4)
lemma sin_sub_cos {A : ℝ} :
    sin A - cos A = √2 * sin (A - π / 4) := by
  -- Use sin angle subtraction formula
  rw [sin_sub]
  norm_num
  ring
  rw [sq_sqrt (by positivity)]
  linarith

-- Introduce a special angle φ
noncomputable abbrev φ := arccos √(1/3)

-- Bound φ
lemma φ_bound : 0 < φ ∧ φ < π / 2 := by
  unfold φ
  constructor
  · -- Lower bound
    rw [arccos_pos]
    nth_rw 2 [show 1 = √1 by simp]
    apply sqrt_lt_sqrt <;> norm_num
  -- Upper bound
  rw [arccos_lt_pi_div_two]
  positivity

-- √2 * cos B + sin B = √3 * sin (B + φ), where φ = arccos √(1/3)
lemma sqrt_two_mul_cos_add_sin {B : ℝ} :
    √2 * cos B + sin B = √3 * sin (B + φ) := by
  -- Use sin angle addition formula
  rw [sin_add]
  unfold φ
  -- Simplify and compute
  rw [cos_arccos (by trans 0 <;> norm_num) (by nth_rw 2 [show 1 = √1 by simp]; apply sqrt_le_sqrt; norm_num), sin_arccos]
  norm_num
  rw [mul_add, mul_comm (√3), mul_assoc, mul_comm (√3), mul_assoc, inv_mul_cancel₀ (by positivity), div_mul_cancel₀ _ (by positivity)]
  linarith

/- 3. In $\triangle A B C$, if $\sin C-\cos C+\sin B=\sqrt{3}$, and $A \geqslant \frac{\pi}{4}$, then $\sin B=$ -/
theorem algebra_281591 (A B C : Real) (hA : A ∈ Set.Icc 0 π)
    (hB : B ∈ Set.Icc 0 π) (hC : C ∈ Set.Icc 0 π) (hABC : A + B + C = π)
    (h : Real.sin C - Real.cos C + Real.sin B = Real.sqrt 3) (hA1 : A ≥ Real.pi / 4) :
    Real.sin B = Real.sqrt 3 / 3 := by
  simp at *
  -- Have an angle inequality
  have h₀ : C - π / 4 ≤ π / 2 - B := by nlinarith
  -- Transform it into an inequality of trig functions
  apply sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) at h₀
  rw [sin_pi_div_two_sub] at h₀
  rw [sin_sub_cos] at h
  -- Prove that sin (B + φ) = 1
  have sin_B_φ_eq_one : sin (B + φ) = 1 := by
    have lb : √3 ≤ √3 * sin (B + φ) := by
      calc
        √3 = √2 * sin (C - π / 4) + sin B := h.symm
        _ ≤ √2 * cos B + sin B := by gcongr
        _ = √3 * sin (B + φ) := sqrt_two_mul_cos_add_sin
    have ub : √3 * sin (B + φ) ≤ √3 := by
      calc
        √3 * sin (B + φ) ≤ √3 * 1 := by gcongr; exact sin_le_one _
        _ = √3 := by simp
    -- Remove the factors of √3
    have : 1 ≤ sin (B + φ) ∧ sin (B + φ) ≤ 1 := by
      constructor
      · nth_rw 1 [← mul_one √3, mul_le_mul_left (by positivity)] at lb
        tauto
      nth_rw 2 [← mul_one √3] at ub
      rw [mul_le_mul_left (by positivity)] at ub
      tauto
    -- By sandwich property, equality is obtained
    linarith
  -- Show that B + φ is π / 2
  have B_add_φ : B + φ = π / 2 := by
    rw [sin_eq_one_iff] at sin_B_φ_eq_one
    rcases sin_B_φ_eq_one with ⟨k, hk⟩
    -- Show that k = 0 by bounding
    have : k = 0 := by
      -- Use contradiction
      by_contra! hk'
      have : k < 0 ∨ 0 < k := lt_or_gt_of_ne hk'
      rcases this with h | h
      · -- Case when k < 0
        have : k ≤ -1 := by linarith
        -- B + φ is positive trivially
        have : B + φ > 0 := by linarith [φ_bound]
        -- B + φ is negative if k is not 0
        have : B + φ ≤ 0 :=
          calc
            B + φ = π / 2 + k * (2 * π) := by tauto
            _ ≤ π / 2 + (-1) * (2 * π) := by gcongr; norm_cast
            _ ≤ 0 := by linarith
        -- We obtain a contradiction
        linarith
      -- Case when 0 < k
      have : 1 ≤ k := by linarith
      -- B + φ < 2 * π by easy bounding
      have : B + φ < 2 * π := by linarith [φ_bound]
      -- B + φ > 2 * π if k is not 0
      have : B + φ > 2 * π := by
        calc
          B + φ = π / 2 + k * (2 * π) := by tauto
          _ ≥ π / 2 + 1 * (2 * π) := by gcongr; norm_cast
          _ > 2 * π := by linarith [pi_pos]
      -- We obtain a contradiction
      linarith
    subst k
    linarith
  rw [← eq_sub_iff_add_eq] at B_add_φ
  calc
    sin B = sin (π / 2 - φ) := by congr
    _ = cos φ := sin_pi_div_two_sub φ
    _ = √(1 / 3) := by unfold φ; rw [cos_arccos (by trans 0 <;> norm_num) (by nth_rw 2 [show 1 = √1 by simp]; apply sqrt_le_sqrt; norm_num)]
    _ = √3 / 3 := by nth_rw 3 [show 3 = √3 * √3 by simp]; rw [div_self_mul_self']; simp