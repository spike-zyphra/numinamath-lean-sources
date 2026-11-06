import Mathlib

theorem algebra_227991 (p q : ℝ) :
    (∃ x, x^3 + p * x + q = 0 ∧ deriv (fun x => x^3 + p * x + q) x = 0) ↔
    (q^2 / 4 + p^3 / 27 = 0) := by
  constructor
  · -- Assume there exists x such that x^3 + p*x + q = 0 and deriv (fun x => x^3 + p * x + q) x = 0, prove q^2 / 4 + p^3 / 27 = 0
    rintro ⟨x, h1, h2⟩
    have h3 : deriv (fun x => x^3 + p * x + q) x = 3 * x^2 + p := by
      simp [deriv_pow, deriv_add, deriv_mul, mul_comm p, mul_assoc]
    rw [h3] at h2
    have hp : p = -3 * x^2 := by linarith
    have hq : q = 2 * x^3 := by
      rw [hp] at h1
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    rw [hq, hp]
    ring_nf
  · -- Assume q^2 / 4 + p^3 / 27 = 0, need to show there exists x such that x^3 + p * x + q = 0 and deriv ... = 0.
    intro h
    have eq1 : 27 * q^2 + 4 * p^3 = 0 := by
      nlinarith
    by_cases hp1 : p = 0
    · 
      have hq1 : q = 0 := by
        rw [hp1] at eq1
        nlinarith
      use 0
      constructor
      · 
        rw [hp1, hq1]
        norm_num
      · 
        rw [hp1]
        norm_num
    · 
      have hp1' : p ≠ 0 := hp1
      use -3 * q / (2 * p)
      constructor
      · 
        have h7 : 27 * q^2 + 4 * p^3 = 0 := by
          linarith
        have eq2 : (-3 * q / (2 * p)) ^ 3 + p * (-3 * q / (2 * p)) + q = 0 := by
          have eq4 : (-3 * q / (2 * p)) ^ 3 + p * (-3 * q / (2 * p)) + q = -27 * q^3 / (8 * p^3) - 3 * q / 2 + q := by
            field_simp [show p ≠ 0 by exact hp1']
            ring
          rw [eq4]
          have eq5 : -27 * q^3 / (8 * p^3) - 3 * q / 2 + q = 0 := by
            have h13 : 27 * q^2 + 4 * p^3 = 0 := by linarith
            have h18 : 27 * q^3 + 4 * p^3 * q = 0 := by
              have h14 : q * (27 * q^2 + 4 * p^3) = 0 := by
                rw [h13]
                norm_num
              nlinarith
            have h19 : -27 * q^3 - 4 * p^3 * q = 0 := by
              linarith
            have eq7 : -27 * q^3 / (8 * p^3) - 3 * q / 2 + q = (-27 * q^3 - 4 * p^3 * q) / (8 * p^3) := by
              field_simp [show p ≠ 0 by exact hp1']
              ring
            rw [eq7]
            rw [show (-27 * q^3 - 4 * p^3 * q : ℝ) = (0 : ℝ) by linarith]
            norm_num
          linarith
        exact eq2
      · 
        have eq10 : deriv (fun x => x^3 + p * x + q) (-3 * q / (2 * p)) = 3 * (-3 * q / (2 * p)) ^ 2 + p := by
          simp [deriv_pow, deriv_add, deriv_mul, mul_comm p, mul_assoc]
        rw [eq10]
        have eq11 : 3 * (-3 * q / (2 * p)) ^ 2 + p = 0 := by
          field_simp [show p ≠ 0 by exact hp1']
          nlinarith
        linarith