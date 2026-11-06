import Mathlib

open Real Set
open scoped Real

/- 2. (3 points) How many different solutions does the equation


$$

10 \sqrt{6} \cos x \cdot \operatorname{ctg} x - 2 \sqrt{6} \operatorname{ctg} x + 5 \cos x - 1 = 0

$$


have on the interval $\left[-\frac{\pi}{2}, \frac{\pi}{2}\right]$? Find these solutions. -/
theorem algebra_186157 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = 10 * sqrt 6 * cos x / tan x - 2 * sqrt 6 / tan x + 5 * cos x - 1) :
    {x | x ∈ Icc (-π/2) (π/2) ∧ tan x ≠ 0 ∧ f x = 0} = {arccos (1/5), -arccos (1/5)} := by
  -- let's simplify this to the equation
  ext x
  simp [h₀]
  -- first let's prove tan of arccos values and bounds on arccos 5⁻¹
  have hct₁ : tan (arccos 5⁻¹) = 2 * √6 := by
    rw [tan_arccos]
    norm_num
    simp [show (25 : ℝ) = 5 ^ 2 by ring, show (24 : ℝ) = 2 ^ 2 * 6 by ring]
  have hct₂ : tan (- arccos 5⁻¹) = -2 * √6 := by
    rw [tan_neg, hct₁]
    norm_num
  have hc_ub : arccos 5⁻¹ < π/2 := by
    apply lt_of_not_ge
    rintro h
    have : cos (arccos 5⁻¹) ≤ 0 := by
      apply cos_nonpos_of_pi_div_two_le_of_le
      . exact h
      . linarith [arccos_le_pi 5⁻¹]
    rw [cos_arccos (by norm_num) (by norm_num)] at this
    norm_num at this
  have hc_lb : -π/2 < arccos 5⁻¹ := by linarith [arccos_nonneg 5⁻¹]
  constructor
  -- now to prove equation implies arccos values
  . rintro ⟨⟨hx_lb, hx_ub⟩, ht, h⟩
    -- factorize to product of two expression
    convert_to (2 * √6 / tan x + 1) * (5 * cos x - 1) = 0 at h
    . ring_nf
      -- so one or both expression is 0
    . simp at h
      obtain h | h := h
      -- first case we have tan x = -2 * √6
      . field_simp at h
        -- as x is not π/2 or -π/2 (otherwise tan x = 0) and that is invalid
        have hx₁ : x ≠ π/2 := by
          by_contra hx
          rw [hx] at h
          simp at h
        have hx₂ : x ≠ -π/2 := by
          by_contra hx
          rw [hx, neg_div, tan_neg] at h
          simp at h
        -- now we get bounds on x that'll help in using injectivity of tan, we also write - 2 * √6 as - arccos 5⁻¹
        replace h : tan x = - 2 * √6 := by linarith
        rw [← hct₂] at h
        have :-π/2 < x := by exact lt_of_le_of_ne hx_lb (id (Ne.symm hx₂))
        have : x < π/2 := by exact lt_of_le_of_ne hx_ub hx₁
        -- we use injectivity of tan to prove x = - arccos 5⁻¹
        have := Real.injOn_tan (x₁ := x) (x₂ := -arccos 5⁻¹) ⟨by linarith, by assumption⟩ ⟨by linarith, by linarith⟩ h
        simp [this]
        -- other case cos x = 5⁻¹
      . replace h : cos x = 5⁻¹ := by linarith
        -- first we prove lemma that x ∈ [0, π/2)
        have aux (x : ℝ) (hx_lb : 0 ≤ x) (hx_ub : x ≤ π/2) (h : cos x = 5⁻¹) : x = arccos 5⁻¹ := by
          rw [← cos_arccos (x := 5⁻¹) (by norm_num) (by norm_num)] at h
          apply Real.injOn_cos
          . exact ⟨hx_lb, by linarith⟩
          . exact ⟨by apply arccos_nonneg, by linarith⟩
          . assumption
        -- now 0 ≤ x, then we can use aux on x to get x = arccos 5⁻¹ and when x < 0 we can use aux on -x to get -x = arccos 5⁻¹
        by_cases hx : 0 ≤ x
        . simp [aux x hx hx_ub h]
        . right
          linarith [aux (-x) (by linarith) (by linarith) (by rwa [← cos_neg] at h)]
    -- in the other direction, we can plug in value in equations, bounds are proved by linarith easily and using tan values that were proved earlier
  . rintro h
    obtain rfl | rfl := h
    . and_intros
      any_goals linarith
      . rw[hct₁]
        simp
      . rw [hct₁, cos_arccos (by norm_num) (by norm_num)]
        norm_num
        ring_nf
        field_simp
    . and_intros
      any_goals linarith
      . rw [hct₂]
        simp
      . rw [hct₂, cos_neg, cos_arccos (by norm_num) (by norm_num)]
        norm_num
        ring_nf
        field_simp