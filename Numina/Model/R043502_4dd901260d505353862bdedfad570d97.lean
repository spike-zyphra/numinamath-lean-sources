import Mathlib

theorem algebra_198161 {p q : ℕ} {R : ℝ} (hp : p.Prime) (hq : q.Prime)
    (hroots : p ≠ q ∧ p^2 - 13 * p + R = 0 ∧ q^2 - 13 * q + R = 0)
    (b : ℕ) (hb : b = p^2 + q^2) :
    b = 125 := by
  rcases hroots with ⟨hpq, hp_eq, hq_eq⟩
  have eq1 : (p : ℝ) ^ 2 - 13 * (p : ℝ) + R = 0 := by 
    simpa using hp_eq
  have eq2 : (q : ℝ) ^ 2 - 13 * (q : ℝ) + R = 0 := by 
    simpa using hq_eq
  have eq3 : (p : ℝ) ^ 2 - (q : ℝ) ^ 2 - 13 * ((p : ℝ) - (q : ℝ)) = 0 := by 
    nlinarith
  have eq4 : ((p : ℝ) - (q : ℝ)) * ((p : ℝ) + (q : ℝ) - 13) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp eq4) with h1 h2
  · -- Case where p = q, which contradicts p ≠ q
    exfalso
    have hp_eq_q : (p : ℝ) = (q : ℝ) := by 
      linarith
    have hp_eq_q_nat : p = q := by 
      exact_mod_cast hp_eq_q
    omega
  · -- Case where p + q = 13
    have hpq13 : (p : ℝ) + (q : ℝ) = 13 := by
      linarith
    have hpq13_nat : p + q = 13 := by 
      exact_mod_cast hpq13
    have h1 : p ≤ 13 := by
      omega
    have h2 : q ≤ 13 := by
      omega
    interval_cases p <;> interval_cases q
      <;> norm_num at hpq13_nat hp hq
      <;> norm_num [hb] at *
      <;> omega