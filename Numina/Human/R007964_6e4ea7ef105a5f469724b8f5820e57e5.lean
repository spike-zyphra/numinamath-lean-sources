import Mathlib

/- Determine all functions $f:(0, \infty) \rightarrow \mathbb{R}$ satisfying  $$ \left(x+\frac{1}{x}\right) f(y)=f(x y)+f\left(\frac{y}{x}\right) $$  for all $x, y>0$.  (South Korea)  Answer: $f(x)=C_{1} x+\frac{C_{2}}{x}$ with arbitrary constants $C_{1}$ and $C_{2}$. -/
theorem algebra_23651 (f : ℝ → ℝ) :
    (∀ x > 0, ∀ y > 0, (x + 1/x) * f y = f (x * y) + f (y / x)) ↔
    ∃ c1 c2, ∀ x > 0, f x = c1 * x + c2 / x := by

    constructor
    · -- 1. we show that every function f satisfying the equation 
      -- has the form f x = c1 * x + c2 / x
      intro hf
      -- Fix a real number a > 1, say a = 2.
      let a : ℝ := 2
      have apos : a > 0 := by unfold a; norm_num

      -- take x = y = t into the equation
      have hf₁ {t : ℝ} (tpos : t > 0) := hf t tpos t tpos

      -- take x = t / a, y = a * t into the equation
      have hf₂ {t : ℝ} (tpos : t > 0) := by
        apply hf (t / a) ?_ (a * t) ?_
        apply div_pos tpos apos
        apply mul_pos apos tpos

      -- take x = a^2 * t, y = t into the equation
      have hf₃ {t : ℝ} (tpos : t > 0) := by
        apply hf (a ^ 2 * t) ?_ t tpos
        apply mul_pos
        exact sq_pos_of_pos apos
        exact tpos

      -- take x = y = a * t into the equation
      have hf₄ {t : ℝ} (tpos : t > 0) := by
        apply hf (a * t) ?h (a * t) ?h
        exact mul_pos apos tpos

      -- take the difference of hf₁ and hf₂ to cancel f (t ^ 2)
      have hf₁₂ {t : ℝ} (tpos : t > 0) :
        (t + 1 / t) * f t - (t / a + a / t) * f (a * t) = f 1 - f (a ^ 2) := by
        have h₁ := hf₁ tpos
        have h₂ := hf₂ tpos
        rw [show t / t = 1 by field_simp] at h₁
        have : t / a * (a * t) = t * t := by field_simp; ring
        rw [this] at h₂
        have : a * t / (t / a) = a * a := by field_simp; ring
        rw [this] at h₂
        have : 1 / (t / a) = a / t := by field_simp
        rw [this] at h₂
        rw [show a * a = a ^ 2 by ring] at h₂
        linear_combination h₁ - h₂

      -- take the difference of hf₃ and hf₄ to cancel f (a ^ 2 * t ^ 2)
      have hf₃₄ {t : ℝ} (tpos : t > 0) :
        (a ^ 2 * t + 1 / (a ^ 2 * t)) * f t - (a * t + 1 / (a * t)) * f (a * t) = f (1 / a ^ 2) - f 1 := by
        have h₃ := hf₃ tpos
        have h₄ := hf₄ tpos
        rw [show t / (a ^ 2 * t) = 1 / a ^ 2 by field_simp; ring] at h₃
        rw [
          show a * t * (a * t) = a ^ 2 * t * t by ring,
          show a * t / (a * t) = 1 by field_simp,
        ] at h₄
        linear_combination h₃ - h₄

      -- take a linear combination of hf₁₂ and hf₃₄ to cancel f (a*t)
      have hf₅ {t : ℝ} (tpos : t > 0) :
        ((a * t + 1 / (a * t)) * (t + 1 / t) - (t / a + a / t) * (a ^ 2 * t + 1 / (a ^ 2 * t)) ) * f t =
          (a * t + 1 / (a * t)) * (f 1 - f (a ^ 2)) - (t / a + a / t) * (f (1 / a ^ 2) - f 1) := by
        have h₁₂ := hf₁₂ tpos
        have h₃₄ := hf₃₄ tpos

        generalize f t = x₁ at h₁₂ h₃₄ ⊢
        generalize f 1 = x₂ at h₁₂ h₃₄ ⊢
        generalize f (a ^ 2) = x₃ at h₁₂ h₃₄ ⊢
        generalize f (1 / (a ^ 2)) = x₄ at h₁₂ h₃₄ ⊢
        generalize f (a * t) = x₅ at h₁₂ h₃₄ ⊢

        field_simp at h₁₂ h₃₄ ⊢

        have tne0 : t ≠ 0 := by exact Ne.symm (ne_of_lt tpos)

        rw [show t * t = t ^ 2 by ring, show a * a = a ^ 2 by ring] at h₁₂
        rw [
          show (t ^ 2 + 1) * x₁ * (a * t) = t * ((a * t ^ 2 + a) * x₁) by ring,
          ← mul_sub,
          show (x₂ - x₃) * (t * (a * t)) = t * ((a * t) * (x₂ - x₃)) by ring,
        ] at h₁₂
        field_simp [tne0] at h₁₂


        have atne0 : a * t ≠ 0 := by
          apply ne_of_gt
          exact mul_pos apos tpos

        nth_rw 1 [mul_comm] at h₃₄
        rw [show a ^ 2 * t * ((a * t * (a * t) + 1) * x₅) = a * t * ((a ^ 3 * t ^ 2 + a) * x₅) by ring] at h₃₄
        rw [← mul_sub] at h₃₄
        rw [show (x₄ - x₂) * (a ^ 2 * t * (a * t)) = a * t * ((a ^ 2 * t) * (x₄ - x₂)) by ring] at h₃₄
        field_simp [atne0] at h₃₄

        apply congrArg (HMul.hMul ((a ^ 3 * t ^ 2 + a) * (a ^ 2 * t ^ 3))) at h₁₂
        apply congrArg (HMul.hMul ((t ^ 2 + a ^ 2) * (a ^ 2 * t ^ 3))) at h₃₄

        linear_combination2 h₁₂ - h₃₄

      -- the coefficient of f t in hf₅ is equal to a + 1 / a - (a ^ 3 + 1 / a ^ 3)
      have h_coef {t : ℝ} (tpos: t > 0) : (a * t + 1 / (a * t)) * (t + 1 / t) - (t / a + a / t) * (a ^ 2 * t + 1 / (a ^ 2 * t)) = a + 1 / a - (a ^ 3 + 1 / a ^ 3) := by field_simp; ring

      -- Denote some constants
      let C := a + 1 / a - (a ^ 3 + 1 / a ^ 3)
      let D := f 1 - f (a ^ 2)
      let E := f (1 / a ^ 2) - f 1

      -- we show that f(x) = ((a * D - E / a) / C) * x + ((D / a - E * a) / C) / x
      use (a * D - E / a) / C
      use (D / a - E * a) / C
      
      intro x xpos

      -- this is done by reforming the equation hf₅
      have hfx := hf₅ xpos
      have hx_coef := h_coef xpos
      rw [hx_coef] at hfx
      rw [show a + 1 / a - (a ^ 3 + 1 / a ^ 3) = C by unfold C; rfl] at hfx
      unfold D E
      field_simp at hfx ⊢
      linear_combination2 (a * C) * hfx

    · -- 2.  we show that f x = c1 * x + c2 / x satisfy the equation
      rintro ⟨c₁, ⟨c₂, hf⟩⟩
      rintro x xpos y ypos
      rw [hf y ypos]
      have xy_pos : x * y > 0 := mul_pos xpos ypos
      have yx_pos : y / x > 0 := div_pos ypos xpos
      rw [hf (x * y) xy_pos, hf (y / x) yx_pos]
      field_simp
      ring
