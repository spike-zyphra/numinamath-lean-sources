import Mathlib

lemma hlm (x y β : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y ^ 3 = x ^ 3) (hβ : β = Complex.exp (2 * Real.pi * Complex.I / 3)) : ∃ s : ℂˣ, (s ^ 3 : ℂ) = 1 ∧ y = x * s ∧ ∃ k : ℕ, k < 3 ∧ s = β ^ k := by
  have h' : IsUnit (y / x) := by
    rw [isUnit_iff_exists]
    use x / y
    field_simp
  -- Let s = y / x, we have s³ = 1.
  let s := h'.unit'
  rw [<-div_eq_one_iff_eq (by field_simp), <-div_pow] at hxy
  replace hxy : (s ^ 3 : ℂ) = 1 := by
    unfold s
    rw [IsUnit.val_unit', hxy]
  have hxy' := hxy
  rw [<-mem_rootsOfUnity' 3, Complex.mem_rootsOfUnity] at hxy
  obtain ⟨k, hk, hxy⟩ := hxy
  -- Show that s = βᵏ.
  have hs' : s = β ^ k := by
    rw [hβ, <-Complex.exp_nat_mul, <-hxy]
    congrm Complex.exp ?_
    ring
  -- We have y = xs.
  have hs : y = x * s := by
    unfold s
    rw [IsUnit.val_unit']
    field_simp
  use s, hxy', hs, k, hk, hs'
  
/- Over all pairs of complex numbers $(x, y)$ satisfying the equations

$$
x+2 y^{2}=x^{4} \quad \text { and } \quad y+2 x^{2}=y^{4}
$$

compute the minimum possible real part of $x$.-/
theorem algebra_610753 :
    IsLeast {a : ℝ | ∃ x y : ℂ, a = x.re ∧ x + 2 * y ^ 2 = x ^ 4 ∧ y + 2 * x ^ 2 = y ^ 4} (-((Real.sqrt 33 - 1) / 2) ^ (1 / 3 : ℝ)) := by
  -- Let β = exp(2πi/3).
  let β := Complex.exp (2 * Real.pi * Complex.I / 3)
  -- Show that β = (-1 + √3i) / 2.
  have hβ₁ : β = (-1 + Real.sqrt 3 * Complex.I) / 2 := by
    unfold β
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    simp
    rw [show (2 * Real.pi / 3 : ℂ) = (2 * Real.pi / 3 : ℝ) by simp, <-Complex.ofReal_cos, <-Complex.ofReal_sin, mul_div_assoc, Real.cos_two_mul, Real.sin_two_mul, Real.cos_pi_div_three, Real.sin_pi_div_three]
    field_simp
    ring
  -- Show that β² = (-1 - √3i) / 2.
  have hβ₂ : β ^ 2 = (-1 - Real.sqrt 3 * Complex.I) / 2 := by
    field_simp [hβ₁]
    ring_nf
    norm_cast
    field_simp
    ring
  -- Split the goal into two parts.
  simp [IsLeast, lowerBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- Verify that such number x that minimizes its real part exists.
    -- Simply take x = x.re = -((Real.sqrt 33 - 1) / 2) ^ (1 / 3 : ℝ).
    let x := (-((Real.sqrt 33 - 1) / 2) ^ (1 / 3 : ℝ) : ℝ)
    use x
    simp [-one_div]
    -- Take y = ((Real.sqrt 33 + 1) / 2) ^ (1 / 3 : ℝ).
    let y := ((Real.sqrt 33 + 1) / 2) ^ (1 / 3 : ℝ)
    use y
    -- Give simple expression to x³ and y³ for later use.
    have hx : x ^ 3 = -((Real.sqrt 33 - 1) / 2) := by
      unfold x
      rw [neg_pow, mul_comm, <-Real.rpow_natCast, <-Real.rpow_mul]
      norm_num
      have h₀ : 1 ≤ Real.sqrt 33 := by
        rw [Real.le_sqrt]
        <;>norm_num
      linarith
    have hy : y ^ 3 = ((Real.sqrt 33 + 1) / 2) := by
      unfold y
      rw [<-Real.rpow_natCast, <-Real.rpow_mul]
      simp
      positivity
    -- Give simple expression to √33 ^ n for later use.
    have h33₃ : Real.sqrt 33 ^3 =33 *Real.sqrt 33 := by
      rw [show 3 = 2 +1 by norm_num, pow_add]
      field_simp
    have h33₄ :Real.sqrt 33 ^4 = 33 ^ 2 := by
      rw [pow_two, show 4 = 2 +2 by norm_num, pow_add]
      field_simp
    have h33₅ : Real.sqrt 33 ^5 = 33 ^2 *Real.sqrt 33 := by
      rw [show 5 = 4 +1 by norm_num, pow_add, h33₄]
      field_simp
    -- It suffices to show that x and y satisfy the original equations.
    refine ⟨?_, ?_⟩
    . -- Show that x + 2y² = x⁴. It suffices to show that 2y³ = xy(x³ - 1).
      suffices 2 * y ^ 2 * y = x * (x ^ 3 - 1) * y by
        have h₀ : y ≠ 0 := by
          by_contra! h₀
          field_simp [y] at h₀
          absurd h₀
          positivity
        norm_cast
        rw [mul_eq_mul_right_iff] at this
        simp [h₀] at this
        linarith only [this]
      rw [hx, show 2 * y ^ 2 * y = 2 * y ^ 3 by ring, hy]
      suffices (2 * ((√33 + 1) / 2)) ^3 = (x * (-((√33 - 1) / 2) - 1) * y)^3 by
        simp [pow_eq_pow_iff_of_ne_zero, show ¬Even 3 by decide] at this
        exact this
      repeat rw [mul_pow]
      rw [hx, hy]
      ring_nf
      field_simp [h33₃, h33₄, h33₅]
      ring
    . -- Show that y + 2x² = y⁴. It suffices to show that 2x³ = xy(y³ - 1).
      suffices 2 * x ^ 2 * x = y * (y ^ 3 - 1) * x by
        have h₀ : x ≠ 0 := by
          by_contra! h₀
          replace h₀ := congr_arg (· ^3 ) h₀
          simp [hx] at h₀
          have h₀ : 1 < Real.sqrt 33 := by
            rw [Real.lt_sqrt]
            <;>norm_num
          linarith
        norm_cast
        rw [mul_eq_mul_right_iff] at this
        simp [h₀] at this
        linarith only [this]
      rw [hy, show 2 * x ^ 2 * x = 2 * x ^ 3 by ring, hx]
      suffices (2 * -((√33 - 1) / 2)) ^3 = (y * ((√33 + 1) / 2 - 1) * x) ^3 by
        simp [pow_eq_pow_iff_of_ne_zero, show ¬Even 3 by decide] at this
        simp [this]
      repeat rw [mul_pow]
      rw [hx, hy]
      ring_nf
      field_simp [h33₃, h33₄, h33₅]
      ring
  . -- Show that such minimum real part exists.
    intro α x hα y h₀ h₁
    set αmin := -((Real.sqrt 33 - 1) / 2) ^ (1 / 3 : ℝ)
    -- Form new equation from h₁x - h₀y.
    have h₂ : (x ^ 3 - y ^3) *(x *y + 2) = 0 := by
      ring_nf
      linear_combination h₁ *x - h₀ *y
    -- Form new equation from h₁y² - h₀x².
    have h₃ : (x ^3 - y ^ 3) *(x ^3 +y ^3 - 1) = 0 := by
      ring_nf
      linear_combination h₁ * y ^ 2 - h₀ *x^2
    simp at h₂ h₃
    -- Show some inequalities involving αmin for later use.
    have g₀ : 0 ≤ Real.sqrt 33 - 1 := by
      rw [sub_nonneg]
      rw [Real.le_sqrt]
      <;> norm_num
    have g₁ : 0 ≤ Real.sqrt 33 - 3 := by
      rw [sub_nonneg]
      rw [Real.le_sqrt]
      <;> norm_num
    have hα₀ : αmin ≤ 0 := by
      simp [αmin]
      positivity
    have hα₁ : αmin ≤ -1 := by
      simp [αmin, -one_div] at hα₀ ⊢
      apply le_of_pow_le_pow_left₀ (show 3 ≠ 0 by norm_num) hα₀
      rw [one_pow, <-Real.rpow_natCast, <-Real.rpow_mul (by positivity)]
      simp
      linarith
    -- Consider cases x = 0 or not.
    by_cases hx : x = 0
    . -- We have x.re = 0 greater than αmin.
      simp [hα, hx, hα₀]
    . -- Show that y ≠ 0 as well.
      have hy : y ≠ 0 := by
        by_contra! hy
        simp [hy, hx] at h₁
      -- Consider cases x³ = y³ or not.
      by_cases h₅ : y ^ 3 = x ^ 3
      . obtain ⟨s, hxy, hs, k, hk, hs'⟩ := hlm x y β hx hy h₅ (by simp [β])
        -- Substitute y = xs into h₀.
        rw [hs] at h₀
        replace h₀ : (x + s) * (x ^ 2 - x * s - s ^ 2) * x = 0:= by
          ring_nf at h₀ ⊢
          simp [hxy]
          linear_combination -h₀
        simp [hx] at h₀
        rcases h₀ with (h₀ | h₀)
        . -- Suppose x + s = 0.
          replace h₀ : x = -s := by
            linear_combination h₀
          interval_cases k
          . -- Suppose k = 0, x = -1.
            simp at hs'
            simp [hα, h₀, hs', hα₁]
          . -- Suppose k = 1, x = -β.
            simp at hs'
            norm_num [hα, h₀, hs', hβ₁]
            exact hα₀.trans (show 0 ≤ (1 / 2 : ℝ) by positivity)
          . -- Suppose k = 2, x = -β².
            norm_num [hα, h₀, hs', hβ₂]
            exact hα₀.trans (show 0 ≤ (1 / 2 : ℝ) by positivity)
        . -- Suppose x² - xs - s² = 0.
          replace h₀ : (2 * x - s + Real.sqrt 5 * s) * (2 * x - s - Real.sqrt 5 * s) = 0 := by
            rw [<-sq_sub_sq, mul_pow]
            norm_cast
            field_simp
            ring_nf
            linear_combination 4 * h₀
          simp at h₀
          rcases h₀ with (h₀ | h₀)
          . -- Suppose x = (1 - √5) / 2 *s.
            replace h₀ : x = (1 - Real.sqrt 5) / 2 *s := by
              linear_combination h₀ / 2
            interval_cases k
            . -- Suppose k = 0, x.re = (1 - √5) / 2.
              simp at hs'
              simp [hα, h₀, hs']
              refine hα₁.trans ?_
              suffices Real.sqrt 5 ≤ 3 by
                linarith
              rw [Real.sqrt_le_iff]
              norm_num
            . -- Suppose k = 1, x.re = (1 - √5) / 2 * (-1 / 2).
              simp [hα, h₀, hs', hβ₁]
              refine hα₀.trans ?_
              suffices 1 ≤ Real.sqrt 5 by
                linarith
              rw [Real.le_sqrt]
              <;> norm_num
            . -- Suppose k = 2, x.re = (1 - √5) / 2 * (-1 / 2).
              norm_num [hα, h₀, hs', hβ₂]
              refine hα₀.trans ?_
              suffices 1 ≤ Real.sqrt 5 by
                linarith
              rw [Real.le_sqrt]
              <;> norm_num
          . -- Suppose x = (1 + √5) / 2 *s.
            replace h₀ : x = (1 + Real.sqrt 5) / 2 *s := by
              linear_combination h₀ / 2
            interval_cases k
            . -- Suppose k = 0, x.re = (1 + √5) / 2.
              simp at hs'
              simp [hα, h₀, hs']
              refine hα₀.trans ?_
              positivity
            . -- Suppose k = 1, x.re = (1 + √5) / 2 * (-1 / 2).
              simp [hα, h₀, hs', hβ₁]
              refine hα₁.trans ?_
              suffices Real.sqrt 5 ≤ 3 by
                linarith
              rw [Real.sqrt_le_iff]
              norm_num
            . -- Suppose k = 2, x.re = (1 + √5) / 2 * (-1 / 2).
              norm_num [hα, h₀, hs', hβ₂]
              refine hα₁.trans ?_
              suffices Real.sqrt 5 ≤ 3 by
                linarith
              rw [Real.sqrt_le_iff]
              norm_num
      . -- We have xy = -2 and x³ + y³ = 1 when x³ ≠ y³.
        push_neg at h₅
        symm at h₅
        simp [sub_eq_zero, h₅] at h₂ h₃
        have h₄ : x ^ 3 *y ^ 3 = -8 := by
          rw [<-mul_pow, show x *y = -2 by linear_combination h₂]
          norm_num
        -- We have (x³)² - (x³) - 8 = 0.
        have h₆ : (x ^ 3) ^ 2 - 1 * x ^3 + -8= 0 := by
          rw [<-h₄, <-h₃]
          ring
        -- We further complete the square.
        replace h₆ : (2 * x ^ 3 - 1) ^ 2 = (Real.sqrt 33) ^ 2 := by
          norm_cast
          field_simp
          linear_combination h₆ * 4
        rw [sq_eq_sq_iff_eq_or_eq_neg] at h₆
        rcases h₆ with (h₆ | h₆)
        . -- We have x³ = (√33 + 1) / 2.
          let γ := ((Real.sqrt 33 + 1) / 2) ^ (1 / 3 : ℝ)
          replace h₆ : x ^ 3 = γ ^ 3 := by
            unfold γ
            norm_cast at h₆ ⊢
            rw [<-Real.rpow_natCast, <-Real.rpow_mul (by positivity)]
            simp
            linear_combination h₆ / 2
          -- Apply the lemma with x ^ 3 = γ ^ 3.
          obtain ⟨s, hxγ, hs, k, hk, hs'⟩ := hlm γ x β (by norm_cast; positivity) hx h₆ (by simp [β])
          interval_cases k
          . -- Suppose k = 0, x = γ.
            simp [hα, hs, hs']
            refine hα₀.trans ?_
            positivity
          . -- Suppose k = 1, x = βγ.
            simp [hα, hs, hs', hβ₁]
            refine hα₁.trans ?_
            suffices γ ≤ 2 by
              linarith
            unfold γ
            rw [<-pow_le_pow_iff_left₀ (by positivity) (by positivity) (show 3 ≠ 0 by norm_num), <-Real.rpow_natCast, <-Real.rpow_mul (by positivity)]
            simp
            suffices Real.sqrt 33 ≤ 15 by
              linarith
            rw [Real.sqrt_le_iff]
            norm_num
          . -- Suppose k = 2, x = β²γ.
            simp [hα, hs, hs', hβ₂]
            refine hα₁.trans ?_
            suffices γ ≤ 2 by
              linarith
            unfold γ
            rw [<-pow_le_pow_iff_left₀ (by positivity) (by positivity) (show 3 ≠ 0 by norm_num), <-Real.rpow_natCast, <-Real.rpow_mul (by positivity)]
            simp
            suffices Real.sqrt 33 ≤ 15 by
              linarith
            rw [Real.sqrt_le_iff]
            norm_num
        . -- We have x³ = -(√33 - 1) / 2.
          replace h₆ : (-x) ^ 3 = (-αmin) ^ 3 := by
            rw [neg_pow]
            nth_rw 2 [neg_pow]
            simp
            unfold αmin
            norm_cast at h₆ ⊢
            rw [neg_pow]
            nth_rw 2 [<-Real.rpow_natCast]
            rw [<-Real.rpow_mul (by positivity)]
            norm_num
            push_cast at h₆
            ring_nf at h₆ ⊢
            linear_combination h₆ / 2
          -- Apply the lemma with (-x) ^ 3 = (-αmin) ^ 3.
          obtain ⟨s, hxγ, hs, k, hk, hs'⟩ := hlm (-αmin) (-x) β (by norm_cast; linarith) (by simp [hx]) h₆ (by simp [β])
          simp at hs
          interval_cases k
          . -- Suppose k = 0, x = αmin.
            simp [hα, hs, hs']
          . -- Suppose k = 1, x = αmin * β.
            simp [hα, hs, hs', hβ₁]
            clear_value αmin
            linarith
          . -- Suppose k = 1, x = αmin * β².
            simp [hα, hs, hs', hβ₂]
            clear_value αmin
            linarith


    
    


    
    
    