import Mathlib

theorem algebra_326384 {f : ℝ → ℝ} (a b p : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0)
    (h : ∀ x, b * (f (x + p) + f x) = a * (1 - f x * f (x + p))) :
    ∃ c, Function.Periodic f c ∧ c ≠ 0 := by

  have eq1 : ∀ x, b * (f (x + p) + f x) = a * (1 - f x * f (x + p)) := h

  have eq2 : ∀ x, (f (x + 2 * p) - f x) * (b + a * f (x + p)) = 0 := by
    intro x
    have eq3 := h (x + p)
    have eq4 := h x
    simp [show (x + p) + p = x + 2 * p by ring] at eq3
    nlinarith

  have eq3 : ∀ x : ℝ, f (x + 2 * p) = f x := by
    intro x
    have eq4 : (f (x + 2 * p) - f x) * (b + a * f (x + p)) = 0 := eq2 x
    cases' (mul_eq_zero.mp eq4) with h1 h2
    · linarith
    · 
      have eq5 : f (x + p) = -b / a := by
        have ha' : a ≠ 0 := ha
        field_simp
        nlinarith
      have eq6 := h x
      rw [eq5] at eq6
      have eq7 : -b ^ 2 = a ^ 2 := by
        have eq8 : b * (-b / a + f x) = a * (1 - f x * (-b / a)) := by
          linarith
        have eq9 : b * (-b / a + f x) = -b ^ 2 / a + b * (f x) := by
          field_simp [ha]
          <;> nlinarith
        have eq10 : a * (1 - f x * (-b / a)) = a + b * (f x) := by
          field_simp [ha]
          <;> nlinarith
        rw [eq9, eq10] at eq8
        have eq11 : -b ^ 2 / a = a := by
          nlinarith
        have eq12 : -b ^ 2 = a ^ 2 := by
          have eq13 : -b^2 / a = a := eq11
          field_simp [ha] at eq13 ⊢
          <;> nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
        exact eq12
      have eq8 : a ^ 2 + b ^ 2 = 0 := by 
        nlinarith [sq_nonneg a, sq_nonneg b]
      have eq9 : a ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact ha
      have eq10 : b ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact hb
      have eq11 : a ^ 2 + b ^ 2 > 0 := by
        positivity
      linarith

  use 2 * p
  constructor
  · unfold Function.Periodic
    intro x
    specialize eq3 x
    linarith
  · 
    intro h1
    have eq4 : p = 0 := by
      linarith
    contradiction