import Mathlib

theorem algebra_286663 {a b : ℚ} (ha : a > 0) (hb : b > 0)
    (h : ∃ q : ℚ, Real.sqrt a + Real.sqrt b = q) :
    ∃ q1 q2 : ℚ, Real.sqrt a = q1 ∧ Real.sqrt b = q2 := by
  rcases h with ⟨q, hq1⟩
  have h1 : Real.sqrt a ≥ 0 := by positivity
  have h2 : Real.sqrt b ≥ 0 := by positivity
  have eq1 : Real.sqrt a = q - Real.sqrt b := by linarith
  have h3 : Real.sqrt b ≥ 0 := by positivity

  have h8 : (2 * (q : ℝ) * Real.sqrt b) = (q ^ 2 - (a : ℝ) + (b : ℝ)) := by
    have h4 : Real.sqrt a ^ 2 = (a : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have eq2 : Real.sqrt a ^ 2 = (q - Real.sqrt b) ^ 2 := by
      rw [show Real.sqrt a = q - Real.sqrt b by linarith]
    rw [h4] at eq2
    have h5 : (q - Real.sqrt b : ℝ) ^ 2 = (q ^ 2 : ℝ) - 2 * (q * Real.sqrt b) + (Real.sqrt b) ^ 2 := by ring
    have h6 : (Real.sqrt b : ℝ) ^ 2 = (b : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    rw [h5] at eq2
    rw [h6] at eq2 
    nlinarith

  have hq : (q : ℝ) ≠ 0 := by
    by_contra h0
    have h0' : (q : ℝ) = 0 := by linarith
    have h1 : Real.sqrt a > 0 := by positivity
    have h2 : Real.sqrt b > 0 := by positivity
    have h3 : Real.sqrt a + Real.sqrt b > 0 := by positivity
    have h4 : (0 : ℝ) > 0 := by
      nlinarith [show Real.sqrt a > 0 by positivity, show Real.sqrt b > 0 by positivity]
    all_goals nlinarith

  have h9 : Real.sqrt b = (q ^ 2 - (a : ℝ) + (b : ℝ)) / (2 * (q : ℝ)) := by
    have h8' : (2 * (q : ℝ) * Real.sqrt b) = (q ^ 2 - (a : ℝ) + (b : ℝ)) := by
      linarith
    field_simp [show (q : ℝ) ≠ 0 by assumption] at h8' ⊢
    nlinarith [Real.sqrt_nonneg b]

  have eq4 : Real.sqrt a = (q - Real.sqrt b : ℝ) := by linarith
  use (q - (q ^ 2 - a + b) / (2 * q)), (q ^ 2 - a + b) / (2 * q)
  constructor
  · -- Prove Real.sqrt a = q1
    rw [show Real.sqrt b = (q ^ 2 - (a : ℝ) + (b : ℝ)) / (2 * (q : ℝ)) by exact_mod_cast h9] at eq4
    field_simp [show (q : ℝ) ≠ 0 by assumption] at eq4 ⊢
    linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  · -- Prove Real.sqrt b = q2
    rw [show Real.sqrt b = (q ^ 2 - (a : ℝ) + (b : ℝ)) / (2 * (q : ℝ)) by exact_mod_cast h9]
    all_goals norm_num