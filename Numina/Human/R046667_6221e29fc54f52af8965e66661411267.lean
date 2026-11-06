import Mathlib

theorem number_theory_4504 (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    IsLeast {d | 0 < d ∧ ∃ x y, d = x * a + y * b} (Int.gcd a b) := by
  simp [IsLeast]
  constructor
  · -- show that gcd(a,b) is positive linear combination of a, b
    constructor
    · exact h.elim (Int.gcd_pos_of_ne_zero_left _) (Int.gcd_pos_of_ne_zero_right _)
    · use (Int.gcdA a b), (Int.gcdB a b)
      rw [mul_comm _ a, mul_comm _ b]
      apply Int.gcd_eq_gcd_ab
  · -- show that gcd(a,b) is the least positive linear combination of a, b
    simp [lowerBounds]
    intro c hc x y hcxy
    -- suffices to show that gcd(a,b) divides any positive linear combination of a, b
    apply Int.le_of_dvd hc
    rw [hcxy]
    apply Int.dvd_add
    · -- gcd(a,b) divides a by definition
      apply Dvd.dvd.mul_left
      apply Int.gcd_dvd_left
    · -- gcd(a,b) divides b by definition
      apply Dvd.dvd.mul_left
      apply Int.gcd_dvd_right
