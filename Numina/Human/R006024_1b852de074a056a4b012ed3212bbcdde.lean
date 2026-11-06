import Mathlib

open Polynomial

/-Let $r, s, t$ be the solutions to the equation $x^{3}+a x^{2}+b x+c=0$. What is the value of $(r s)^{2}+(s t)^{2}+(r t)^{2}$ in terms of $a, b$, and $c$ ?-/
theorem algebra_611157 (a b c r s t : ℝ) : let P : Polynomial ℝ := X ^ 3 + C a * X ^ 2 + C b * X + C c
P.roots = {r, s, t} → (r * s) ^ 2 + (s * t) ^ 2 + (r * t) ^ 2 = b ^ 2 - 2 * a * c := by
-- Denote the polynomial in question by $P$, prove that the natDegree of $P$ is $3$
  intro P Prt; have ndegP : P.natDegree = 3 := by
    rw [← show ((X:ℝ[X])^3).natDegree = 3 by rw [natDegree_X_pow]]
    dsimp [P]; rw [add_assoc, add_assoc]; apply natDegree_add_eq_left_of_natDegree_lt
    rw [natDegree_X_pow, ← add_assoc, natDegree_add_C]
    by_cases ha : a ≠ 0
    · rw [natDegree_add_eq_left_of_natDegree_lt]; calc
        _ ≤ 2 := by apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
      rw [natDegree_C_mul_X_pow, show X = X^1 by simp]; calc
        _ ≤ 1 := by apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
      exact ha
    simp at ha; simp [ha]; calc
        _ ≤ 1 := by rw [show X = X^1 by simp]; apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
-- Prove that $P$ is monic
  have Pmo : P.Monic := by
    dsimp [P]; rw [Monic, add_assoc, add_assoc, leadingCoeff_add_of_degree_lt']
    rw [leadingCoeff_X_pow]; rw [degree_X_pow, degree_lt_iff_coeff_zero]
    intro m hm; apply coeff_eq_zero_of_natDegree_lt; apply lt_of_lt_of_le _ hm
    rw [← add_assoc, natDegree_add_C]; by_cases ha : a ≠ 0
    · rw [natDegree_add_eq_left_of_natDegree_lt]; calc
        _ ≤ 2 := by apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
      rw [natDegree_C_mul_X_pow, show X = X^1 by simp]; calc
        _ ≤ 1 := by apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
      exact ha
    simp at ha; simp [ha]; calc
        _ ≤ 1 := by rw [show X = X^1 by simp]; apply natDegree_C_mul_X_pow_le
        _ < _ := by simp
-- Prove that $P$ splits
  have Psp : P.Splits (RingHom.id ℝ):= by
    rw [splits_iff_card_roots, Prt, ndegP]; simp
-- Rewrite $P$ as a product of linear polynomials, then compare the coefficients to find relations between $(a, b, c)$ and $(r, s, t)$
  have Pprod := eq_prod_roots_of_monic_of_splits_id Pmo Psp
  simp [Prt] at Pprod; dsimp [P] at Pprod
  rw [show (X-C r)*((X-C s)*(X-C t)) = X^3+-(C r+C s+C t)*X^2+(C r*C s+C s*C t+C t*C r)*X+-C r*C s*C t by ring] at Pprod
  simp [ext_iff] at Pprod; have c0 := Pprod 0; have c1 := Pprod 1; have c2 := Pprod 2;
  simp at c0 c1 c2; replace c1 : b = r * s + s * t + t * r := by
    simp [c1]; repeat rw [← C_neg]
    rw [← C_add, ← C_add, coeff_C_mul_X_pow]; simp
  replace c2 : a = -(r + s + t) := by
    simp [coeff_X] at c2; repeat rw [← C_neg] at c2
    rw [← C_add, ← C_add, coeff_C_mul_X_pow] at c2; simp at c2
    rw [c2]; ring
-- Plug these relations to the final goal
  rw [c0, c1, c2]; ring