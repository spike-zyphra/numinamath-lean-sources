import Mathlib

/-$A$ and $B$ are constants such that
$$\frac{4x+5}{x^2+x-2}= \frac{A}{x+2} +\frac{B}{x-1}. $$Find $$\frac{B}{x+1} - \frac{A}{x-2}.$$-/
theorem algebra_21511 {A B : ℝ} (h : ∀ x, x + 2 ≠ 0 → x - 1 ≠ 0 → (4 * x + 5) / (x ^ 2 + x - 2) = A / (x + 2) + B / (x - 1)) :
    ∀ x, x + 1 ≠ 0 → x - 2 ≠ 0 → B / (x + 1) - A / (x - 2) = (2 * x - 7) / ((x + 1) * (x - 2)) := by
    have e₁ : ∀ (x : ℝ), (x ^ 2 + x - 2) = (x + 2) * (x - 1) := fun x => by ring
    have h₁ : ∀ x, x + 2 ≠ 0 → x - 1 ≠ 0 → 4 * x + 5 = (A + B) * x - (A - 2 * B) := by -- Multipying both sides by (x+1)(x-2)
      intro x hx₁ hx₂
      have := h x hx₁ hx₂
      rw [e₁] at this
      field_simp at this
      rw [this]
      ring
    -- Comparing coefficients
    have e₂ := h₁ 0 (by norm_num) (by norm_num)
    ring_nf at e₂
    have e₃ := h₁ 2 (by norm_num) (by norm_num)
    ring_nf at e₃
    -- Solve these equations
    have e₄ : (5:ℝ) + 13 = 18 := by norm_num
    have e₅ : (13:ℝ) - 5 * 2 = 3 := by norm_num
    rw [e₂, e₃] at e₄ e₅
    ring_nf at e₄ e₅
    rw [← eq_div_iff (by norm_num)] at e₄
    rw [← eq_div_iff (by norm_num)] at e₅
    norm_num at e₄ e₅
    intro x _ _
    rw [e₄, e₅] --Substitute A,B
    field_simp
    ring