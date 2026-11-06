import Mathlib

theorem algebra_97791 {a b c p : ℝ} (ha : a ≠ 0) (hp : p ≠ 0)
  (hv0 : a * p ^ 2 + b * p + c = p)
  (hv1 : p = - b / (2 * a))
  (hi : c = -p) :
b = 4 := by
  rw [hi] at hv0
  have eq1 : a * p ^ 2 + b * p - 2 * p = 0 := by
    nlinarith
  have eq2 : p * (a * p + b - 2) = 0 := by
    linarith
  have eq3 : a * p + b - 2 = 0 := by
    apply (mul_left_inj' hp).mp
    linarith
  have eq4 : 2 * a * p = -b := by
    have h1 : 2 * a ≠ 0 := by
      intro h
      apply ha
      linarith
    have h2 : p = -b / (2 * a) := hv1
    field_simp [h1] at h2 ⊢
    linarith
  have eq5 : a * p = 2 - b := by
    linarith
  have eq7 : 2 * (a * p) = -b := by
    linarith [eq4]
  rw [eq5] at eq7
  linarith