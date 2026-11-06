import Mathlib

theorem algebra_194181 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a = 1 / (1 / a + 1 / b) + 1 / (1 / a + 1 / c) + 1 / (1 / b + 1 / c))
    (h2 : 1 / b = 1 / (1 / a + 1 / b) + 1 / (1 / a + 1 / c) + 1 / (1 / b + 1 / c))
    (h3 : 1 / c = 1 / (1 / a + 1 / b) + 1 / (1 / a + 1 / c) + 1 / (1 / b + 1 / c)) :
    1 / a = 2 / (a + b) ∧ 1 / b = 2 / (a + c) ∧ 1 / c = 2 / (b + c) := by

  have eq1 : 1 / (1 / a + 1 / b) = a * b / (a + b) := by
    have h1 : a + b ≠ 0 := by nlinarith
    field_simp
    <;> ring
  have eq2 : 1 / (1 / a + 1 / c) = a * c / (a + c) := by
    have h1 : a + c ≠ 0 := by nlinarith
    field_simp
    <;> ring
  have eq3 : 1 / (1 / b + 1 / c) = b * c / (b + c) := by
    have h1 : b + c ≠ 0 := by nlinarith
    field_simp
    <;> ring

  have eq4 : 1 / a = (a * b / (a + b)) + (a * c / (a + c)) + (b * c / (b + c)) := by
    rw [eq1] at h1
    rw [eq2] at h1
    rw [eq3] at h1
    linarith
  have eq5 : 1 / b = (a * b / (a + b)) + (a * c / (a + c)) + (b * c / (b + c)) := by
    rw [eq1] at h2
    rw [eq2] at h2
    rw [eq3] at h2
    linarith
  have eq6 : 1 / c = (a * b / (a + b)) + (a * c / (a + c)) + (b * c / (b + c)) := by
    rw [eq1] at h3
    rw [eq2] at h3
    rw [eq3] at h3
    linarith

  have eq7 : 1 / a = 1 / b := by
    linarith [eq4, eq5]

  have eq8 : 1 / a = 1 / c := by
    linarith [eq4, eq6]

  have eq9 : a = b := by
    have h1 : 1 / a = 1 / b := eq7
    have h2 : a ≠ 0 := by linarith
    have h3 : b ≠ 0 := by linarith
    field_simp at h1 ⊢
    <;> linarith

  have eq10 : a = c := by
    have h1 : 1 / a = 1 / c := eq8
    have h2 : a ≠ 0 := by linarith
    have h3 : c ≠ 0 := by linarith
    field_simp at h1 ⊢
    <;> linarith

  have eq11 : 1 / a = 2 / (a + b) := by
    have h1 : b = a := by
      linarith [eq9]
    rw [show b = a by linarith]
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith

  have eq12 : 1 / b = 2 / (a + c) := by
    have h1 : b = a := by
      linarith [eq9]
    have h2 : c = a := by
      linarith [eq10]
    rw [show b = a by linarith, show c = a by linarith]
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith

  have eq13 : 1 / c = 2 / (b + c) := by
    have h1 : c = a := by
      linarith [eq10]
    have h2 : b = a := by
      linarith [eq9]
    rw [show c = a by linarith, show b = a by linarith]
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith

  constructor
  · exact eq11
  constructor
  · exact eq12
  · exact eq13