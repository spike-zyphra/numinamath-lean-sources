import Mathlib

theorem algebra_2753 {a : ℝ} (ha : a ≠ 1 ∧ a ≠ -1) (f : ℝ → ℝ)
    (hf : ∀ x > 0, 0 < f x) (h : ∀ x > 0, a * x ^ 2 * f (1 / x) + f x = x / (1 + x)) :
    ∀ x > 0, f x = (x * (a * x - 1)) / ((a ^ 2 - 1) * (x + 1)) := by
  intro x hx
  have eq1 := h x hx
  have eq2 := h (1 / x) (by positivity)
  field_simp [show x ≠ 0 by linarith] at eq1 eq2
  have eq4 : a ^ 2 - 1 ≠ 0 := by
    have h1 : a ≠ 1 := ha.1
    have h2 : a ≠ -1 := ha.2
    have h3 : a ^ 2 - 1 ≠ 0 := by
      intro h'
      have eq1 : a ^ 2 = 1 := by linarith
      have eq2 : a = 1 ∨ a = -1 := by
        rw [sq_eq_one_iff] at eq1
        tauto
      cases eq2 with
      | inl h3 =>
        tauto
      | inr h3 =>
        tauto
    exact h3
  have eq3 : f x = (x * (a * x - 1)) / ((a ^ 2 - 1) * (x + 1)) := by
    have hfx_pos : 0 < f x := hf x hx
    have hfx_pos_x : 0 < 1 / x := by positivity
    have hfx_pos_x : 0 < 1 / x := by positivity
    field_simp [eq4, show x + 1 ≠ 0 by nlinarith, show x ≠ 0 by linarith] at eq1 eq2 ⊢
    nlinarith [hf (x) hx, hf (1 / x) (by positivity), sq_pos_of_pos hx, sq_pos_of_pos (show 0 < x + 1 by nlinarith), sq_nonneg (f x), sq_nonneg (f (1 / x)), sq_nonneg (x ^ 2), sq_nonneg (a ^ 2), sq_pos_of_ne_zero (show x ≠ 0 by linarith), sq_pos_of_ne_zero eq4, sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  exact eq3