import Mathlib

open Polynomial

theorem algebra_21847 {b c : ℝ} (h : (X ^ 2 + C b * X + C b) ∣ (X ^ 3 + 2 * X ^ 2 + 2 * X + C c)) : b = 1 ∨ b = 2 := by
-- Let $p$ be the other factor
  rcases h with ⟨p, hp⟩
  -- $\deg(X ^ 3 + 2 * X ^ 2 + 2 * X + C c) = \deg((X ^ 2 + C b * X + C b) * p)$
  have degeq : (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).natDegree = ((X ^ 2 + C b * X + C b) * p).natDegree := by
    rw [hp]
  -- $\deg(X ^ 3 + 2 * X ^ 2 + 2 * X + C c) = 3$
  have deg1 : (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).natDegree = 3 := by
    compute_degree!
  -- $\deg(X ^ 2 + C b * X + C b) = 2$
  have deg2 : (X ^ 2 + C b * X + C b).natDegree = 2 := by
    compute_degree!
  -- $X ^ 2 + C b * X + C b \neq 0$
  have neq : X ^ 2 + C b * X + C b ≠ 0 := by
    intro h
    simp [h] at deg2
  -- $p \neq 0$
  have pneq : p ≠ 0 := by
    intro h
    simp [h, deg1] at degeq
  rw [natDegree_mul neq pneq, deg1, deg2] at degeq
  -- $p$ is linear
  have degp : p.natDegree = 1 := by
    omega
  -- $p$ is monic
  have pmonic : Monic p := by
    refine Monic.of_mul_monic_left (p := X ^ 2 + C b * X + C b) ?_ ?_
    . simp [Monic.def, ← coeff_natDegree, deg2]
    . simp [← hp, Monic.def, ← coeff_natDegree, deg1, coeff_X_of_ne_one]
  -- $p = X + r$
  have peq := Monic.eq_X_add_C pmonic degp
  rw [peq] at hp
  -- $b + r = 2$
  have eq1 : (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).coeff 2 = ((X ^ 2 + C b * X + C b) * (X + C (p.coeff 0))).coeff 2 := by
    show (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).coeff 2 = ((X ^ 2 + C b * X + C b) * (X + C (p.coeff 0))).coeff 2
    rw [hp]
  ring_nf at eq1
  simp [coeff_X_of_ne_one, coeff_C] at eq1
  -- $b + br = 2$
  have eq2 : (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).coeff 1 = ((X ^ 2 + C b * X + C b) * (X + C (p.coeff 0))).coeff 1 := by
    show (X ^ 3 + 2 * X ^ 2 + 2 * X + C c).coeff 1 = ((X ^ 2 + C b * X + C b) * (X + C (p.coeff 0))).coeff 1
    rw [hp]
  ring_nf at eq2
  simp [coeff_X_of_ne_one, coeff_C] at eq2
  have : b^2 - 3 * b + 2 = 0 := by
    nlinarith
  have : (b - 1) * (b - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp this) with h1 h2
  . left
    linarith
  . right
    linarith