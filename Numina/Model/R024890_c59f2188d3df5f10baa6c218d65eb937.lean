import Mathlib

theorem algebra_183577 (r s t : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hroots : (s^2 + r * s + s = 0 ∧ t^2 + r * t + s = 0)) (h5root : 5^2 + t * 5 + r = 0) :
    s = 29 ∨ s = -6 := by
  rcases hroots with ⟨hs1, ht1⟩
  have h_eq1 : s * (s + r + 1) = 0 := by
    nlinarith 
  cases (mul_eq_zero.mp h_eq1) with
  | inl h1 =>
    exfalso
    exact hs (by linarith)
  | inr h2 =>
    have h_eq2 : s = -r - 1 := by linarith
    have h_eq3 : r = -25 - 5 * t := by
      linarith
    have h_eq4 : s = 24 + 5 * t := by
      rw [h_eq3] at h_eq2
      linarith
    rw [h_eq4] at ht1
    rw [h_eq3] at ht1
    have h_eq5 : t ^ 2 + 5 * t - 6 = 0 := by
      nlinarith
    have h_eq6 : (t + 6) * (t - 1) = 0 := by
      linarith [h_eq5]
    cases (mul_eq_zero.mp h_eq6) with
    | inl h7 =>
      have ht2 : t = -6 := by linarith
      have hs2 : s = -6 := by
        rw [ht2] at h_eq4
        linarith
      right
      linarith
    | inr h8 =>
      have ht2 : t = 1 := by linarith
      have hs2 : s = 29 := by
        rw [ht2] at h_eq4
        linarith
      left
      linarith