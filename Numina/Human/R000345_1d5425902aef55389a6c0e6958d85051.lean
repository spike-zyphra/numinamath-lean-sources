import Mathlib

open Real Set
open scoped BigOperators

/-
  The function $f(x)=x^2-2x$, with $x\in [-2,4]$, has an increasing interval of ______, and $f(x)_{max}=$______.
-/
theorem algebra_9027 {f : ℝ → ℝ} (hf : f = λ x => x ^ 2 - 2 * x) :
    IsGreatest (image f (Icc (-2) 4)) 8 ∧
    StrictMonoOn f (Icc 1 4) := by
  constructor
  · -- prove 8 is maximal
    simp [IsGreatest, upperBounds]
    constructor
    · -- use -2 to obtain 8
      use -2
      simp
      constructor
      · norm_num
      · simp [hf]
        ring
    · -- prove f (x) ≤ 8
      intro y x hx1 hx2 hfx
      rw [<-hfx]
      simp [hf]
      -- i.e. (x - 1) ^ 2 ≤ 7
      suffices : (x - 1) ^ 2 ≤ 9
      · linarith
      · suffices h : x - 1 ≥ -√ 9 ∧ x - 1 ≤ √ 9
        · refine (Real.sq_le ?this.h).mpr ?this.a
          · simp
          · constructor
            · exact h.left
            · exact h.right
        · -- prove |x - 1| ≤ 3
          have : √ 9 = 3 := by
            refine sqrt_eq_cases.mpr ?_
            apply Or.inl
            constructor <;> linarith
          simp only [this]
          constructor
          · calc
              x - 1 ≥ - 2 - 1 := by rel [hx1]
              _ = -3 := by norm_num
          · calc
              x - 1 ≤ 4 - 1 := by rel [hx2]
              _ = 3 := by norm_num
  · -- show f is mono on [1, 4]
    intro x₁ hx₁ x₂ hx₂ hlt
    -- simplify
    have : f x₂ - f x₁ = (x₂ - x₁) * (x₂ + x₁ - 2) := by
      simp [hf]
      ring
    have : f x₂ - f x₁ > 0 := by
      rw [this]
      apply mul_pos
      · exact sub_pos.mpr hlt
      · simp at hx₁ hx₂
        linarith
    exact lt_add_neg_iff_lt.mp this
