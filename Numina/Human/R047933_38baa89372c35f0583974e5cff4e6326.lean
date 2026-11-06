import Mathlib

/- 2. (ROM) For which real numbers $x$ do the following equations hold: (a) $\sqrt{x+\sqrt{2 x-1}}+\sqrt{x+\sqrt{2 x-1}}=\sqrt{2}$, (b) $\sqrt{x+\sqrt{2 x-1}}+\sqrt{x+\sqrt{2 x-1}}=1$, (c) $\sqrt{x+\sqrt{2 x-1}}+\sqrt{x+\sqrt{2 x-1}}=2$ ? -/
theorem other_24471 {x c : ℝ} (hx : x ≥ 1 / 2) (ha : c = Real.sqrt (x + Real.sqrt (2 * x - 1)) + Real.sqrt (x - Real.sqrt (2 * x - 1))) :
    (c = Real.sqrt 2 ↔ x ≤ 1) ∧ c ≠ 1 ∧ (c = 2 ↔ x = 3 / 2) := by
  -- Prove that x + √(2x - 1) ≥ 0.
  have h₀ : x + Real.sqrt (2 * x - 1) ≥ 0 := by
    linarith only [hx, show Real.sqrt (2 * x - 1) ≥ 0 by positivity]
  -- Prove that x - √(2x - 1) ≥ 0.
  have h₁ : x - Real.sqrt (2 * x - 1) ≥ 0 := by
    simp
    rw [<-@abs_of_nonneg _ _ _ (Real.sqrt (2 * x - 1))]
    apply abs_le_of_sq_le_sq
    rw [Real.sq_sqrt]
    linarith only [show (x - 1) ^ 2 ≥ 0 by positivity]
    linarith only [hx]
    linarith only [hx]
    positivity
  have h₂ : c ≥ 0 := by
    rw [ha]
    positivity
  rw [<-sq_eq_sq (by rw [ha]; positivity) (by positivity), add_sq, Real.sq_sqrt h₁, Real.sq_sqrt h₀, mul_assoc, <-Real.sqrt_mul h₀, <-sq_sub_sq, Real.sq_sqrt (by linarith only [hx])] at ha
  ring_nf at ha
  rw [show 1 - x * 2 + x ^ 2 = (x - 1) ^ 2 by ring_nf, <-sq_abs (x - 1), Real.sqrt_sq (by positivity)] at ha
  -- Address the three subquestions.
  refine ⟨?_, ?_, ?_⟩
  . -- Show that c = √2 ↔ x ≤ 1. (Under the prior assumption that x ≥ 1 / 2).
    rw [<-sq_eq_sq h₂ (by norm_num), ha]
    norm_num
    apply Iff.intro
    <;> intro h₃
    . rw [<-abs_neg] at h₃
      replace h₃ : x * 2 + |-(x - 1)| * 2 = x * 2 + (1 - x) * 2 := h₃.trans (by ring_nf)
      simp at h₃
      exact h₃
    . simp [abs, h₃, show x - 1 ≤ 1 - x by linarith only [h₃]]
      ring_nf
  . -- Show that c = 1 implies no solution / contradiction.
    by_contra! h₃
    rw [h₃] at ha
    by_cases h₄ : x ≤ 1
    . simp [abs, h₄, show x - 1 ≤ 1 - x by linarith only [h₄]] at ha
      linarith only [ha]
    . simp at h₄
      simp [abs, h₄, show 1 - x ≤ x - 1 by linarith only [h₄]] at ha
      linarith
  . -- Show that c = 2 ↔ x = 3 / 2.
    apply Iff.intro
    <;> intro h₃
    . rw [h₃] at ha
      by_cases h₄ : x ≤ 1
      . simp [abs, h₄, show x - 1 ≤ 1 - x by linarith only [h₄]] at ha
        linarith only [ha]
      . simp at h₄
        simp [abs, h₄, show 1 - x ≤ x - 1 by linarith only [h₄]] at ha
        linarith only [ha]
    . rw [h₃] at ha
      simp [abs] at ha
      norm_num at ha
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num] at ha
      rw [sq_eq_sq h₂ (by norm_num)] at ha
      exact ha

