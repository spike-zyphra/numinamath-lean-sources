import Mathlib

theorem algebra_206802 {a q r : ℝ} (ha : a ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) 
    (hqr : q + r ≠ 0) (h : ∃ s : ℝ, s ≠ 0 ∧ 
      a * (q + r) = (a + a) * s ∧ 
      a * (q^2 + r^2) = a * (q + r) * s) :
    q = r := by
  rcases h with ⟨s, hs, h1, h2⟩
  have eq1 : a * (q + r) = 2 * a * s := by
    linarith
  have h3 : q + r = 2 * s := by
    apply (mul_left_inj' ha).mp
    linarith
  have h4 : s = (q + r) / 2 := by
    linarith
  have eq2 : a * (q^2 + r^2) = a * (q + r) * s := by
    linarith
  have eq3 : q^2 + r^2 = (q + r) * s := by
    apply (mul_left_inj' ha).mp
    linarith [eq2]
  rw [h4] at eq3
  have eq4 : 2 * (q^2 + r^2) = (q + r) ^ 2 := by
    nlinarith
  have eq5 : (q - r) ^ 2 = 0 := by
    nlinarith
  have eq6 : q - r = 0 := by
    nlinarith
  linarith