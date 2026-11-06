import Mathlib

theorem number_theory_95971 {P P' D R R' r r' : ℕ} (hR : R = P % D)
    (hR' : R' = P' % D) (hr : r = (P * P') % D) (hr' : r' = (R * R' % D)) :
    r = r' := by 
  rw [hr, hr', hR, hR']
  <;> simp [Nat.mul_mod]
  all_goals omega