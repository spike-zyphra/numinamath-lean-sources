import Mathlib

theorem algebra_22553 {a b : ℝ} (h : Polynomial.X ^ 2 - 2 * Polynomial.X - 1 ∣ (Polynomial.X ^ 6 + Polynomial.C a * Polynomial.X + Polynomial.C b)) :
    a + b = -99 := by
  rcases h with ⟨h1, heq⟩
  have eq1 : (1 + Real.sqrt 2) ^ 6 + a * ((1 + Real.sqrt 2) ) + b = 0 := by
    have eq1' : Polynomial.eval ((1 + Real.sqrt 2) : ℝ) (Polynomial.X ^ 6 + Polynomial.C a * Polynomial.X + Polynomial.C b) = Polynomial.eval ((1 + Real.sqrt 2) : ℝ) ((Polynomial.X ^ 2 - 2 * Polynomial.X - 1) * h1) := by 
      rw [heq]
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at eq1' ⊢
    ring_nf at eq1' ⊢
    <;> norm_num [pow_two, pow_succ] at eq1' ⊢
    all_goals 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq2 : (1 - Real.sqrt 2) ^ 6 + a * ((1 - Real.sqrt 2) ) + b = 0 := by
    have eq2' : Polynomial.eval ((1 - Real.sqrt 2) : ℝ) (Polynomial.X ^ 6 + Polynomial.C a * Polynomial.X + Polynomial.C b) = Polynomial.eval ((1 - Real.sqrt 2) : ℝ) ((Polynomial.X ^ 2 - 2 * Polynomial.X - 1) * h1) := by 
      rw [heq]
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at eq2' ⊢
    ring_nf at eq2' ⊢
    <;> norm_num [pow_two, pow_succ] at eq2' ⊢
    all_goals 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq1' : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq1'' : (1 + Real.sqrt 2) ^ 4 = 17 + 12 * Real.sqrt 2 := by
    calc
      (1 + Real.sqrt 2) ^ 4 = ((1 + Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (3 + 2 * Real.sqrt 2) ^ 2 := by rw [eq1']
      _ = 17 + 12 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h11 : (1 + Real.sqrt 2) ^ 6 = 99 + 70 * Real.sqrt 2 := by
    calc
      (1 + Real.sqrt 2) ^ 6 = ((1 + Real.sqrt 2) ^ 4) * ((1 + Real.sqrt 2) ^ 2) := by ring
      _ = (17 + 12 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) := by rw [eq1'', eq1']
      _ = 99 + 70 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq1''' : (1 - Real.sqrt 2) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have eq1'''' : (1 - Real.sqrt 2) ^ 4 = 17 - 12 * Real.sqrt 2 := by
    calc
      (1 - Real.sqrt 2) ^ 4 = ((1 - Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (3 - 2 * Real.sqrt 2) ^ 2 := by rw [eq1''']
      _ = 17 - 12 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h12 : (1 - Real.sqrt 2) ^ 6 = 99 - 70 * Real.sqrt 2 := by
    calc
      (1 - Real.sqrt 2) ^ 6 = ((1 - Real.sqrt 2) ^ 4) * ((1 - Real.sqrt 2) ^ 2) := by ring
      _ = (17 - 12 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) := by rw [eq1'''', eq1''']
      _ = 99 - 70 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h11] at eq1
  rw [h12] at eq2
  have eq3 : (99 + a + b) + (70 + a) * Real.sqrt 2 = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  have eq4 : (99 + a + b) = 0 := by
    have h0 : Real.sqrt 2 > 0 := by
      positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  have eq5 : (70 + a) = 0 := by
    have h0 : Real.sqrt 2 > 0 := by
      positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  have h3 : a = -70 := by linarith
  have h4 : b = -29 := by
    rw [h3] at eq4
    linarith
  linarith [h3, h4]