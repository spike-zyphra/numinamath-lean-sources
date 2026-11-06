import Mathlib

theorem algebra_142651 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b) (h : ∀ x, f (f (f x)) = 8 * x + 7) :
    f = fun x => 2 * x + 1 := by 
  rcases hf with ⟨a, b, hfab⟩
  have eq1 := h 0
  simp [hfab] at eq1
  have eq2 := h 1
  simp [hfab] at eq2
  have ha1 : a^3 = 8 := by
    nlinarith
  have ha2 : a = 2 := by
    have h1 : a^3 - 8 = 0 := by linarith
    have h2 : (a - 2) * (a^2 + 2 * a + 4) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with ha3 ha4
    · -- ha3 is a - 2 = 0, so a = 2
      linarith
    · -- ha4 is a^2 + 2*a + 4 = 0
      have h5 : a^2 + 2 * a + 4 > 0 := by 
        nlinarith [sq_nonneg (a + 1)]
      nlinarith [h5, ha4]
  have hb : b = 1 := by
    rw [ha2] at eq1
    nlinarith
  ext x
  simp [hfab, ha2, hb]
  all_goals nlinarith