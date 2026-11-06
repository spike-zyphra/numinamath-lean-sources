import Mathlib

open Polynomial
theorem algebra_611267 {p q r a b: ℝ} {f: ℝ[X]} (hf: f = X ^ 3 - C a * X ^ 2 + C b * X - C 48) (hmo: f.Monic)
(h_pos: 0 < p) (h_lt: p < q) (h_lt2: q < r) (h_roots: f.roots = [p, q, r]) :
(1/p + 2/q + 3/r ≥ 3/2) ∧ (∃ P Q R A B: ℝ, (0 < P) ∧ (P < Q) ∧ (Q < R) ∧ (P^3-A*P^2+B*P-48=0) ∧
(Q^3-A*Q^2+B*Q-48=0) ∧ (R^3-A*R^2+B*R-48=0) ∧ (1/P + 2/Q + 3/R = 3/2)) := by
  constructor
  have prod_eq: p * q * r = 48 := by
      have h_deg: f.natDegree = 3 := by
        rw [hf]
        compute_degree!
      have h_root_card: f.roots.card = 3 := by
        rw [h_roots]
        simp
      have h_0_coeff: f.coeff 0 = -48 := by
        rw [hf]
        norm_num
      have splits: f.roots.card = f.natDegree := by
        simp [h_deg,h_root_card]
      rw [← Polynomial.splits_iff_card_roots] at splits
      have h:= Polynomial.prod_roots_eq_coeff_zero_of_monic_of_splits hmo splits -- apply vieta theorem --
      simp only [h_deg,h_0_coeff,h_roots] at h
      simp [Multiset.prod] at h
      ring_nf at h
      nlinarith
  -- good! now we obtain the relationships. so go to solving the problem.--
  have ineq: (1/p + 2/q + 3/r) ≥ 3/2 := by
    have hp1: 0 < p * q * r := by
      nlinarith [h_pos,show 0 < q by linarith,show 0 < r by linarith]
    have hp2: 0 < p*q := by
      nlinarith [h_pos,show 0 < q by linarith]
    have hp3: 0 < r := by linarith
    -- good! all denominator will vanish, so we can multiply the terms --
    have mul_ineq: ((1/p + 2/q + 3/r) - 3/2) ≥ 0 := by
        have hp3': r > 0 := by linarith
        have hp2': q > 0 := by linarith
        have hp1': p > 0 := by linarith
        field_simp
        rw [prod_eq]
        nlinarith [sq_nonneg (p - 2), sq_nonneg (q - 4), sq_nonneg (r - 6), sq_nonneg (p*q - 8), sq_nonneg (p*r - 12), sq_nonneg (q*r - 24), sq_nonneg (p*q*r - 48)]
    linarith
  exact ineq
  use 2
  use 4
  use 6
  use (12)
  use (44)
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  norm_num