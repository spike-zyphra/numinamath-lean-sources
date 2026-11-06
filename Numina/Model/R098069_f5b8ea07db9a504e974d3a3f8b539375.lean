import Mathlib

theorem other_91421 {f : ℝ → ℝ} (hf : ∀ x, f x ≠ 0)
    (h : ∀ x, f (x + 2) = f (x - 1) * f (x + 5)) :
    ∀ x, f (x + 18) = f x := by
  intro x
  have eq1 : ∀ x, f (x + 5) = f (x + 2) * f (x + 8) := by
    intro x
    specialize h (x + 3)
    rw [show x + 3 + 2 = x + 5 by ring] at h
    rw [show x + 3 - 1 = x + 2 by ring] at h
    rw [show x + 3 + 5 = x + 8 by ring] at h
    linarith
  have eq3 : ∀ x, f (x - 1) * f (x + 8) = 1 := by
    intro x
    have eq5 := h x
    have eq6 := eq1 x
    rw [eq6] at eq5
    have h1 : f (x + 2) ≠ 0 := hf (x + 2)
    have eq4 : f (x - 1) * f (x + 8) = 1 := by
      apply (mul_left_inj' h1).mp
      linarith
    exact eq4
  have eq4' : ∀ x, f x * f (x + 9) = 1 := by
    intro x
    have eq5 := eq3 (x + 1)
    have eq6 : (x + 1) - 1 = x := by ring
    have eq7 : (x + 1) + 8 = x + 9 := by ring
    rw [eq6] at eq5
    rw [eq7] at eq5
    linarith
  have eq8 : ∀ x, f (x + 9) = 1 / f x := by
    intro x
    have eq9 := eq4' x
    have eq10 : f x ≠ 0 := hf x
    field_simp [eq9]
    <;> nlinarith
  have eq12 : ∀ x, f (x + 18) = 1 / f (x + 9) := by
    intro x
    have eq13 := eq4' (x + 9)
    have eq14 : (x + 9) + 9 = x + 18 := by ring
    rw [eq14] at eq13
    have eq15 : f (x + 9) ≠ 0 := hf (x + 9)
    field_simp [eq13]
    <;> nlinarith
  have eq16 : f (x + 18) = f x := by
    have eq17 := eq12 x
    have eq18 := eq8 x
    rw [eq18] at eq17
    have eq19 : f x ≠ 0 := hf x
    field_simp [eq19] at eq17 ⊢
    <;> nlinarith
  exact eq16