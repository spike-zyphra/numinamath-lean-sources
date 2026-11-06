import Mathlib

theorem algebra_96129 {A m s : ℝ} (hA : A > 0) (hm : m = 0.2 * (A - s)) (hs : s = 0.05 * (A - m)) :
round (((m + s) / A) * 100) = 23 := by
  have eq1 : 5 * m + s = A := by
    have eq1 : m = 0.2 * (A - s) := hm
    ring_nf at eq1 ⊢
    nlinarith
  have eq2 : 20 * s + m = A := by
    have eq2 : s = 0.05 * (A - m) := hs
    ring_nf at eq2 ⊢
    nlinarith
  have eq3 : 4 * m = 19 * s := by
    nlinarith
  have eq4 : s = (4 / 99) * A := by
    have eq1' : 5 * m + s = A := eq1
    have eq3' : 4 * m = 19 * s := eq3
    have eq5 : m = (19 / 4) * s := by
      linarith
    rw [eq5] at eq1'
    linarith
  have eq6 : m = (19 / 99) * A := by
    have eq5 : m = (19 / 4) * s := by
      have eq3' : 4 * m = 19 * s := eq3
      linarith
    rw [eq5, eq4]
    field_simp at *
    <;> linarith
  have eq7 : m + s = (23 / 99) * A := by
    have eq6' : m = (19 / 99) * A := eq6
    have eq4' : s = (4 / 99) * A := eq4
    linarith
  have h1 : ((m + s) / A) * 100 = (2300 / 99) := by
    rw [eq7]
    have h2 : A ≠ 0 := by linarith
    field_simp at *
    <;> nlinarith
    <;> linarith
  rw [h1]
  norm_num [round_eq]
  <;> norm_num
  <;> linarith