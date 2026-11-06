import Mathlib

theorem inequalities_86473 (a b c d : ℝ) : a^2 + b^2 + c^2 + d^2 = a * b + b * c + c * d + d * a → a = b ∧ b = c ∧ c = d := by
  intro h
  have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 = 0 := by
    nlinarith
  have h2 : (a - b) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h3 : (b - c) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h4 : (c - d) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h5 : (d - a) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h6 : (a - b) ^ 2 = 0 := by
    linarith [h1, h2, h3, h4, h5]
  have h7 : (b - c) ^ 2 = 0 := by
    linarith [h1, h2, h3, h4, h5]
  have h8 : (c - d) ^ 2 = 0 := by
    linarith [h1, h2, h3, h4, h5]
  have h9 : (d - a) ^ 2 = 0 := by
    linarith [h1, h2, h3, h4, h5]
  have h10 : a - b = 0 := by
    rwa [sq_eq_zero_iff] at h6
  have h11 : b - c = 0 := by
    rwa [sq_eq_zero_iff] at h7
  have h12 : c - d = 0 := by
    rwa [sq_eq_zero_iff] at h8
  have h13 : d - a = 0 := by
    rwa [sq_eq_zero_iff] at h9
  have ha1 : a = b := by linarith
  have hb1 : b = c := by linarith
  have hc1 : c = d := by linarith
  exact ⟨ha1, hb1, hc1⟩