import Mathlib

theorem number_theory_131524 (x y t : ℤ) (hx : x^2 = 151 - 15 * t^2) (hy : y = 3 * t)
    (h : 3 * x^2 + 5 * y^2 = 453) :
    (x = 4 ∧ y = 9) ∨ (x = -4 ∧ y = -9) ∨ (x = 4 ∧ y = -9) ∨ (x = -4 ∧ y = 9) := by
  have h1 : t^2 ≤ 10 := by
    nlinarith [sq_nonneg x, sq_nonneg t, hx]

  have h2 : t ≥ -3 := by
    nlinarith [sq_nonneg (t + 3), h1]

  have h3 : t ≤ 3 := by
    nlinarith [sq_nonneg (t - 3), h1]
  interval_cases t <;> try { 
    norm_num at hx 
    have h4 : x ≤ 12 := by nlinarith [sq_nonneg x, hx]
    have h5 : x ≥ -12 := by nlinarith [sq_nonneg x, hx]
    interval_cases x <;> norm_num at hx <;> simp [hy] at *
    <;> tauto
  }