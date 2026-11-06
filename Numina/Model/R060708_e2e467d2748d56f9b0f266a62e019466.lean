import Mathlib

theorem number_theory_252546 {P P' D R R' r r' : ℕ} (hP : P > P') (hD : D ≠ 0)
    (hPR : P % D = R ∧ P' % D = R') (hr : (P * P') % D = r ∧ (R * R') % D = r') :
    r = r' := by
  have h1 : P % D = R := hPR.1
  have h2 : P' % D = R' := hPR.2
  have h3 : (P * P') % D = r := hr.1
  have h4 : (R * R') % D = r' := hr.2
  have h5 : (P * P') % D = (R * R') % D := by
    rw [Nat.mul_mod, h1, h2]
  linarith [h3, h4, h5]