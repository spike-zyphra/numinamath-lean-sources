import Mathlib

theorem algebra_123193 {f : ℝ → ℝ} (hf : ∃ p : Polynomial ℝ, p.degree = 2 ∧ ∀ x, f x = p.eval x)
    (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h : f a = b * c ∧ f b = c * a ∧ f c = a * b) :
    f (a + b + c) = a * b + b * c + c * a := by
  rcases hf with ⟨p, hp2, h1⟩
  rcases h with ⟨ha1, hb1, hc1⟩
  rcases hdist with ⟨ha2, hb2, hc2⟩
  have eq1 : p.eval a = b * c := by linarith [ha1, h1 a]
  have eq2 : p.eval b = c * a := by linarith [hb1, h1 b]
  have eq3 : p.eval c = a * b := by linarith [hc1, h1 c]
  have eq4 : f (a + b + c) = p.eval (a + b + c) := by
    apply h1
  have h2 : p.natDegree = 2 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp2]
  have eq5 : p.eval a = p.coeff 2 * a ^ 2 + p.coeff 1 * a + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h2, Finset.sum_range_succ, pow_succ, mul_assoc]
    all_goals ring
  have eq6 : p.eval b = p.coeff 2 * b ^ 2 + p.coeff 1 * b + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h2, Finset.sum_range_succ, pow_succ, mul_assoc]
    all_goals ring
  have eq7 : p.eval c = p.coeff 2 * c ^ 2 + p.coeff 1 * c + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h2, Finset.sum_range_succ, pow_succ, mul_assoc]
    all_goals ring
  rw [eq5] at eq1
  rw [eq6] at eq2
  rw [eq7] at eq3
  have eq8 : p.coeff 2 * (a ^ 2 - b ^ 2) + p.coeff 1 * (a - b) = b * c - c * a := by
    nlinarith
  have eq9 : (a - b) * (p.coeff 2 * (a + b) + p.coeff 1) = -c * (a - b) := by
    nlinarith [eq8]
  have eq10 : p.coeff 2 * (a + b) + p.coeff 1 = -c := by
    apply (mul_left_inj' (show (a - b) ≠ 0 by
      intro h'
      apply ha2
      linarith
    )).mp
    linarith
  have eq11 : p.coeff 2 * (b ^ 2 - c ^ 2) + p.coeff 1 * (b - c) = c * a - a * b := by
    nlinarith
  have eq12 : (b - c) * (p.coeff 2 * (b + c) + p.coeff 1) = -a * (b - c) := by
    nlinarith [eq11]
  have eq13 : p.coeff 2 * (b + c) + p.coeff 1 = -a := by
    apply (mul_left_inj' (show (b - c) ≠ 0 by
      intro h'
      apply hc2
      linarith
    )).mp
    linarith
  have eq14 : p.coeff 2 * (a - c) = a - c := by
    nlinarith [eq10, eq13]
  have eq15 : p.coeff 2 = 1 := by
    apply (mul_left_inj' (show (a - c) ≠ 0 by
      intro h'
      apply hb2
      linarith
    )).mp
    linarith
  have eq16 : p.coeff 1 = -(a + b + c) := by
    rw [eq15] at eq10
    nlinarith
  have eq17 : p.coeff 0 = a * b + b * c + c * a := by
    rw [eq15, eq16] at eq1
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
  have eq18 : p.eval (a + b + c) = p.coeff 2 * (a + b + c) ^ 2 + p.coeff 1 * (a + b + c) + p.coeff 0 := by
    simp [Polynomial.eval_eq_sum_range, h2, Finset.sum_range_succ, pow_succ, mul_assoc]
    all_goals ring
  rw [eq4]
  rw [eq18]
  rw [eq15, eq16, eq17]
  ring