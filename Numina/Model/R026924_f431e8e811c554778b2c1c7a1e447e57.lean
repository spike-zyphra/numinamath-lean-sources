import Mathlib

theorem algebra_193328 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (4 / a + 3 / b = 1) ∧ (12 / a - 3 / b = 1)) :
    a = 8 := by
  rcases h with ⟨h1, h2⟩
  have eq3 : 4 * b + 3 * a = a * b := by
    have h11 : a ≠ 0 := ha
    have h12 : b ≠ 0 := hb
    field_simp [h11, h12] at h1
    linarith
  have eq4 : 12 * b - 3 * a = a * b := by
    have h11 : a ≠ 0 := ha
    have h12 : b ≠ 0 := hb
    field_simp [h11, h12] at h2
    linarith
  have eq5 : 16 * b = 2 * a * b := by
    nlinarith [eq3, eq4]
  have eq6 : b * (a - 8) = 0 := by
    have eq7 : 2 * a * b - 16 * b = 0 := by
      linarith [eq5]
    have eq8 : 2 * b * (a - 8) = 0 := by
      linarith [eq7]
    have eq9 : b * (a - 8) = 0 := by
      nlinarith
    exact_mod_cast eq9
  cases' (mul_eq_zero.mp eq6) with h7 h8
  · -- b = 0
    exfalso
    apply hb
    linarith
  · -- a - 8 = 0
    linarith