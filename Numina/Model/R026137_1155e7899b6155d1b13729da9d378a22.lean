import Mathlib

theorem algebra_212617 {f : ℝ → ℝ} (h : ∀ x, f x + (0.5 + x) * f (1 - x) = 1) :
    (∀ x, x ≠ 0.5 → f x = 1 / (0.5 - x)) ∧ f 0.5 = 0.5 := by
  have h1 : f 0.5 = 0.5 := by
    have eq1 := h 0.5
    norm_num at eq1 ⊢
    linarith [eq1]
  have h2 : ∀ x, x ≠ 0.5 → f x = 1 / (0.5 - x) := by
    intro x hx
    have eq1 := h x
    have eq2 := h (1 - x)
    have eq3 : f x + (0.5 + x) * f (1 - x) = 1 := by
      simpa using eq1
    have eq4 : f (1 - x) + (0.5 + (1 - x) ) * f x = 1 := by
      simpa using eq2
    have eq5 : (x - 0.5) * (f x + f (1 - x)) = 0 := by
      ring_nf at eq3 eq4 ⊢
      nlinarith
    cases' (mul_eq_zero.1 eq5) with eq6 eq7
    · -- x - 0.5 = 0
      exfalso
      have hx' : x = 0.5 := by
        norm_num at eq6 ⊢
        linarith
      tauto
    · -- f x + f (1 - x) = 0
      have eq8 : f (1 - x) = -f x := by
        linarith
      rw [eq8] at eq3
      have eq9 : f x * (0.5 - x) = 1 := by
        ring_nf at eq3 ⊢
        nlinarith
      have hx2 : x - 0.5 ≠ 0 := by
        intro h
        apply hx
        linarith
      have hx3 : 0.5 - x ≠ 0 := by
        by_contra h
        have : x = 0.5 := by
          norm_num at h ⊢
          linarith
        tauto
      field_simp [hx3] at *
      linarith
  constructor
  · -- ∀ x, x ≠ 0.5 → f x = 1 / (0.5 - x)
    exact h2
  · -- f 0.5 = 0.5
    exact h1