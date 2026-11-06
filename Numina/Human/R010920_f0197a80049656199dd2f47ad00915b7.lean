import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_609456 : Set.ncard {(x, y, z) : ℤ×ℤ×ℤ | -10 ≤ x ∧ x ≤ 10 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -10 ≤ z ∧ z ≤ 10 ∧ ∃a b c : ℝ, a * b = x ∧ a * c = y ∧ b * c = z} = 4061 := by
  have h₁ : {(x, y, z) : ℤ×ℤ×ℤ | -10 ≤ x ∧ x ≤ 10 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -10 ≤ z ∧ z ≤ 10 ∧ ∃a b c : ℝ, a * b = x ∧ a * c = y ∧ b * c = z} = {(x, y, z) : ℤ×ℤ×ℤ | -10 ≤ x ∧ x ≤ 10 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -10 ≤ z ∧ z ≤ 10 ∧ (0 < x * y * z ∨ (x = 0 ∧ y = 0) ∨ (x = 0 ∧ z = 0) ∨ (y = 0 ∧ z = 0))} := by
    ext ⟨x, y, z⟩
    constructor <;> simp
    · intro hx₁ hx₂ hy₁ hy₂ hz₁ hz₂
      intro a b hx₃ c hy₃ hz₃
      split_ands
      all_goals repeat linarith
      by_cases hx₄ : x = 0
      · rw [hx₄] at hx₃ ⊢
        norm_num at hx₃ ⊢
        obtain (ha | hb) := hx₃
        · -- a = 0
          rw [ha, Eq.comm] at hy₃
          simp at hy₃
          apply Or.inl
          exact hy₃
        · -- b = 0
          rw [hb, Eq.comm] at hz₃
          simp at hz₃
          apply Or.inr
          apply Or.inl
          exact hz₃
      by_cases hy₄ : y = 0
      · rw [hy₄] at hy₃ ⊢
        norm_num at hy₃ ⊢
        obtain (ha | hc) := hy₃
        · -- a = 0
          rw [ha, Eq.comm] at hx₃
          simp at hx₃
          apply Or.inl
          exact hx₃
        · -- c = 0
          rw [hc, Eq.comm] at hz₃
          simp at hz₃
          apply Or.inr
          apply Or.inr
          exact hz₃
      by_cases hz₄ : z = 0
      · rw [hz₄] at hz₃ ⊢
        norm_num at hz₃ ⊢
        obtain (hb | hc) := hz₃
        · -- b = 0
          rw [hb, Eq.comm] at hx₃
          simp at hx₃
          apply Or.inr
          apply Or.inl
          exact hx₃
        · -- c = 0
          rw [hc, Eq.comm] at hy₃
          simp at hy₃
          apply Or.inr
          apply Or.inr
          exact hy₃
      apply Or.inl
      suffices 0 < (x * y * z : ℝ) by norm_cast at this
      suffices (x * y * z) = (a * b * c) ^ 2 by
        rw [this]
        apply sq_pos_of_ne_zero
        intro habc
        simp at habc
        obtain ((ha | hb) | hc) := habc
        · -- a = 0
          rw [ha, Eq.comm] at hx₃
          simp at hx₃
          exact hx₄ hx₃
        · -- b = 0
          rw [hb, Eq.comm] at hx₃
          simp at hx₃
          exact hx₄ hx₃
        · -- c = 0
          rw [hc, Eq.comm] at hy₃
          simp at hy₃
          exact hy₄ hy₃
      rw [←hx₃, ←hy₃, ←hz₃]
      ring_nf
    · intro hx₁ hx₂ hy₁ hy₂ hz₁ hz₂
      intro h₁
      split_ands
      all_goals repeat linarith
      obtain (hpos | h₁) := h₁
      · set a := √(x * y / z) with ha
        set b := √(x * z / y) with hb
        set c := √(y * z / x) with hc
        have hx₃ : x ≠ 0 := by
          intro this
          rw [this] at hpos
          norm_num at hpos
        have hy₃ : y ≠ 0 := by
          intro this
          rw [this] at hpos
          norm_num at hpos
        have hz₃ : z ≠ 0 := by
          intro this
          rw [this] at hpos
          norm_num at hpos
        have hab : a * b = |x| := by
          rw [ha, hb, ←Real.sqrt_mul, Real.sqrt_eq_iff_eq_sq]
          have : x * y / z * (x * z / y : ℝ) = x^2 := by
            field_simp
            ring_nf
          rw [this, Eq.comm]
          norm_cast
          rw [sq_abs]
          apply mul_nonneg
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          norm_cast
          linarith [abs_nonneg x]
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
        have hac : a * c = |y| := by
          rw [ha, hc, ←Real.sqrt_mul, Real.sqrt_eq_iff_eq_sq]
          have : x * y / z * (y * z / x : ℝ) = y^2 := by
            field_simp
            ring_nf
          rw [this, Eq.comm]
          norm_cast
          rw [sq_abs]
          apply mul_nonneg
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          norm_cast
          linarith [abs_nonneg y]
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
        have hbc : b * c = |z| := by
          rw [hb, hc, ←Real.sqrt_mul, Real.sqrt_eq_iff_eq_sq]
          have : x * z / y * (y * z / x : ℝ) = z^2 := by
            field_simp
            ring_nf
          rw [this, Eq.comm]
          norm_cast
          rw [sq_abs]
          apply mul_nonneg
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
          norm_cast
          linarith [abs_nonneg z]
          rw [div_nonneg_iff, ←mul_nonneg_iff]
          norm_cast
          linarith
        use a
        by_cases hx₄ : x < 0
        · rw [abs_eq_neg_self.mpr (by linarith)] at hab
          use -b
          norm_num at hab ⊢
          rw [hab]
          norm_num
          by_cases hy₄ : y < 0
          · use -c
            rw [abs_eq_neg_self.mpr (by linarith)] at hac
            norm_num at hac ⊢
            rw [hac]
            norm_num
            rw [hbc]
            norm_num
            have hxy : 0 < x * y := by exact Int.mul_pos_of_neg_of_neg hx₄ hy₄
            by_contra! hz
            absurd hpos
            simp
            apply Int.mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          push_neg at hy₄
          rw [abs_eq_self.mpr hy₄] at hac
          use c
          rw [hac]
          norm_num
          rw [hbc, abs_eq_neg_self.mpr]
          norm_num
          by_contra! hz
          absurd hpos
          simp
          have hxy : x * y ≤ 0 := by
            apply Int.mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          apply Int.mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        push_neg at hx₄
        rw [abs_eq_self.mpr hx₄] at hab
        use b
        rw [hab]
        norm_num
        by_cases hy₄ : y < 0
        · use -c
          rw [abs_eq_neg_self.mpr (by linarith)] at hac
          norm_num at hac ⊢
          rw [hac]
          norm_num
          rw [hbc, abs_eq_neg_self.mpr]
          norm_num
          by_contra! hz
          absurd hpos
          simp
          have hxy : x * y ≤ 0 := by
            apply Int.mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          apply Int.mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        push_neg at hy₄
        use c
        rw [abs_eq_self.mpr hy₄] at hac
        rw [hac]
        norm_num
        rw [hbc]
        norm_num
        by_contra! hz
        absurd hpos
        simp
        apply Int.mul_nonpos_of_nonneg_of_nonpos
        apply Int.mul_nonneg (by linarith) (by linarith)
        linarith
      · obtain (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) := h₁ <;>
          rw [h₁, h₂] <;>
          norm_num
        · use 0
          use 1
          norm_num
        · use 1
          use 0
          norm_num
        · use x
          use 1
          norm_num
  have h₂ : {(x, y, z) : ℤ×ℤ×ℤ | -10 ≤ x ∧ x ≤ 10 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -10 ≤ z ∧ z ≤ 10 ∧ (0 < x * y * z ∨ (x = 0 ∧ y = 0) ∨ (x = 0 ∧ z = 0) ∨ (y = 0 ∧ z = 0))} = Finset.filter (λ(x, y, z) ↦ (0 < x * y * z ∨ (x = 0 ∧ y = 0) ∨ (x = 0 ∧ z = 0) ∨ (y = 0 ∧ z = 0))) (Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10) 10 ×ˢ Finset.Icc (-10) 10) := by
    ext ⟨x, y, z⟩; simp
    tauto
  rw [h₁, h₂, Set.ncard_coe_Finset]
  native_decide
