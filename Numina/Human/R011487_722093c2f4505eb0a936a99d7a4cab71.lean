import Mathlib

open Real

/- 2. Solve the inequality $\frac{\sqrt[6]{4 x^{2}}-\sqrt[3]{x^{2}}}{\left(x^{2}-2|x|\right)^{2}+4|x|-2 x^{2}-3} \leqslant 0$. -/
theorem algebra_148197 : {x : ℝ | ((x ^ 2 - 2 * |x|) ^ 2 + 4 * |x| -2 * x ^ 2 - 3) ≠ 0 ∧ ((4 * x ^ 2) ^ (1 / 6 : ℝ) - (x ^ 2) ^ (1 / 3 : ℝ)) / ((x ^ 2 - 2 * |x|) ^ 2 + 4 * |x| -2 * x ^ 2 - 3) ≤ 0}  = {x : ℝ | x <
 -3 ∨ (-2 ≤ x ∧ x < -1) ∨ (-1 < x ∧ x < 1) ∨ (1 < x ∧ x ≤ 2) ∨ x > 3} := by
  ext x
  -- Simplify the denominator to (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2
  have h_simp_de_1 : (x ^ 2 - 2 * |x|) ^ 2 + 4 * |x| - 2 * x ^ 2 - 3 =
    (x ^ 2 - 2 * |x| - 3) * (x ^ 2 - 2 * |x| + 1) := by nlinarith
  have h_simp_de_2 : (x ^ 2 - 2 * |x| - 3) = (|x| - 3) * (|x| + 1):=by
    rw [← Even.pow_abs (by simp), pow_two]
    ring_nf
  have h_simp_de_3 : (x ^ 2 - 2 * |x| + 1) = (|x| - 1) ^ 2 := by nlinarith
  -- Simplify the numerator to (2 * |x|) ^ {1/3} - (x ^ 2) ^ {1/3}
  have h_simp_nu_1 : (4 * x ^ 2) ^ (6⁻¹ : ℝ) = (2 * |x|) ^ (3⁻¹ : ℝ) := by
    have h_simp_nu_2 : 4 * x ^ 2 = (2 * |x|) ^ (2 : ℝ) :=by
      rw [mul_rpow (by norm_num) (by positivity)]
      norm_num
    rw [h_simp_nu_2]
    rw [←Real.rpow_mul (by norm_num : 0 ≤ 2 * |x|) 2 (6⁻¹)]
    norm_num
  -- Simplify the equation
  simp [h_simp_de_2,h_simp_de_3,h_simp_de_1,h_simp_nu_1]
  have h_de_2_over_zero : |x| + 1 > 0 := by linarith [abs_nonneg x]
  constructor
  · -- Forward direction
      rintro ⟨⟨⟨h11,h12⟩, h13⟩, h14⟩
      have h_de_23_over_zero :  0 < (|x| + 1) * (|x| - 1) ^ 2 := by positivity
      -- Prove |x| $\neq$ 1
      have h13 : ¬x = 1 ∧ ¬x = -1 := by
        by_contra! h
        apply h13
        by_cases hx : x = 1
        · simp [hx]
        · simp [h hx]
      rw [div_nonpos_iff] at h14
      rcases h14 with ⟨h15 , h16⟩ | ⟨h17 , h18⟩
      -- Case denominator $\leq$  0 and numerator $\geq$ 0
      · simp at h15
        -- Prove |x| $\leq$ 2
        have h_about_2_1 : -2 ≤ x ∧ x ≤ 2 := by
          rw [Real.rpow_le_rpow_iff] at h15
          · rw [← abs_le]
            rw [← sq_abs] at h15
            by_cases hx : 0 = |x|
            · linarith
            · rw [←div_le_iff₀, pow_two] at h15
              have hy : |x| * |x| / |x| = |x| := by field_simp [hx]
              rw [hy] at h15
              exact h15
              apply lt_of_le_of_ne (abs_nonneg x)
              simp
              exact hx
          · nlinarith
          · norm_num
          · norm_num
        -- Prove (|x| $\leq$ 2 and |x| $\neq$ 1) can show the target
        by_cases hx1 : x < -1
        -- Part [-2 , -1)
        · simp [h_about_2_1.left, hx1]
        . by_cases hx2 : x > 1
          -- Part (1, 2]
          · simp [hx2, h_about_2_1.right]
          -- Part (-1 , 1)
          . simp at hx1 hx2
            have hx11 : -1 < x := by exact lt_of_le_of_ne hx1 (Ne.symm h13.right)
            have hx12 : x < 1 := by exact lt_of_le_of_ne hx2 h13.left
            simp [hx11, hx12]
      -- Case denominator $\geq$ 0 and numerator $\leq$ 0
      · --Prove |x| > 3
        have h_about_3_2 : x > 3 ∨ x < -3 := by
          have h_de_1_over_zero : 0 < |x| - 3:= by
            have h_de_1_over_zero : 0 ≤ |x| - 3 := by
              apply (mul_le_mul_right h_de_23_over_zero).mp (by linarith)
            exact lt_of_le_of_ne h_de_1_over_zero (Ne.symm h11)
          simp at h_de_1_over_zero
          have hz := lt_abs.mp h_de_1_over_zero
          rcases hz with (hpos | hneg)
          · left
            exact hpos
          · right
            linarith
        -- Prove (|x| > 3) can deduce the target
        rcases h_about_3_2 with (h3l | h3r)
        -- Part (3, $\infty$)
        · simp [h3l]
        -- Part (-$\infty$,-3)
        · simp [h3r]
  · -- Backward direction
    intro h2
    constructor
    -- denominator $\neq 0$
    · rcases h2 with (h21 | h22 | h23 | h24 | h25)
      <;> exact ⟨⟨by nlinarith, by linarith⟩, by nlinarith⟩
    -- The inequality is true
    · have h_de_3_over_zero_2 : (|x| - 1) ^ 2 > 0 := by
        suffices |x| - 1 ≠ 0 by exact pow_two_pos_of_ne_zero this
        by_contra h
        rw [sub_eq_zero, abs_eq (by norm_num)] at h
        rcases h2 with (h21 | h22 | h23 | h24 | h25)
        <;> rcases h with (h1 | h2)
        <;> linarith
      rcases h2 with (h21 | h22 | h23 | h24 | h25)
      · -- Case when $x < -3$, Prove denominator > 0
        have denominator_over_zero_1 : (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2 > 0 := by
          apply mul_pos (mul_pos _ (by positivity)) (by positivity)
          nlinarith
        -- Prove numerator < 0
        have numerator_less_zero_1 : (2 * |x|) ^ (3⁻¹ : ℝ) - (x ^ 2) ^ (3⁻¹ :ℝ) < 0 := by
          rw [abs_of_neg (by linarith)]
          simp
          exact Real.rpow_lt_rpow (by linarith) (by nlinarith) (by norm_num)
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith) 
      · -- Case when $-2 \leq x$ and $x < -1$, first Prove denominator < 0
        have denominator_less_zero_2 : (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2 < 0 := by
          apply mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by nlinarith) h_de_2_over_zero) h_de_3_over_zero_2
        -- Prove numerator $\geq 0$
        have numerator_over_zero_2 : (2 * |x|) ^ (3⁻¹ : ℝ) - (x ^ 2) ^ (3⁻¹ :ℝ) ≥ 0:= by
          rw [abs_of_neg (by linarith)]
          simp
          apply Real.rpow_le_rpow (by nlinarith) (by nlinarith) (by norm_num)
        exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)  
      · -- Case when $-1 < x$ and $x < 1$, first Prove denominator < 0
        have h23_abs : 0 ≤ |x| ∧ |x| < 1 := by exact ⟨abs_nonneg x ,abs_lt.mpr h23⟩
        have denominator_less_zero_5 : (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2 < 0 := by
          exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by nlinarith) h_de_2_over_zero) h_de_3_over_zero_2
        -- Prove numerator ≥ 0
        have numerator_over_zero_5: (2 * |x|) ^ (3⁻¹ : ℝ) - (x ^ 2) ^ (3⁻¹ : ℝ) ≥ 0 := by
          simp
          apply Real.rpow_le_rpow (by nlinarith) (by nlinarith) (by norm_num)
        exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      · -- Case when $1 < x$ and $x \leq 2$, first Prove denominator < 0
        have denominator_less_zero_4 : (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2 < 0 := by
          exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by nlinarith) h_de_2_over_zero) h_de_3_over_zero_2
        -- Prove numerator $\geq 0$
        have numerator_over_zero_4 : (2 * |x|) ^ (3⁻¹ : ℝ) - (x ^ 2) ^ (3⁻¹ :ℝ) ≥ 0 := by
          rw [abs_of_pos (by linarith)]
          simp
          apply Real.rpow_le_rpow (by nlinarith) (by nlinarith) (by norm_num)
        exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
      · -- Case when $x > 3$, first Prove denominator > 0
        have denominator_over_zero_5 : (|x| - 3) * (|x| + 1) * (|x| - 1) ^ 2 > 0 := by
          apply mul_pos (mul_pos _ (by positivity)) (by positivity)
          nlinarith
        -- Prove numerator $\leq 0$
        have numerator_less_zero_5 : (2 * |x|) ^ (3⁻¹ : ℝ) - (x ^ 2) ^ (3⁻¹ :ℝ) < 0 := by
          rw [abs_of_pos (by linarith)]
          simp
          apply Real.rpow_lt_rpow (by linarith) (by nlinarith) (by norm_num)
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)