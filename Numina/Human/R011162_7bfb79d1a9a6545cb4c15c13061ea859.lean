import Mathlib

open Polynomial
/-Suppose x^3 -a*x^2 + b*x - 48 = 0 is a polynomial with three positive roots p, q, and r
such that p < q < r. What is the minimum possible value of 11/p + 2/q + 3/r?-/
theorem algebra_611267 {p q r a b: ℝ} {f: ℝ[X]} (hf: f = X ^ 3 - C a * X ^ 2 + C b * X - C 48) (hmo: f.Monic)
(h_pos: 0 < p) (h_lt: p < q) (h_lt2: q < r) (h_roots: f.roots = [p, q, r]) :
(1/p + 2/q + 3/r ≥ 3/2) ∧ (∃ P Q R A B: ℝ, (0 < P) ∧ (P < Q) ∧ (Q < R) ∧ (P^3-A*P^2+B*P-48=0) ∧
(Q^3-A*Q^2+B*Q-48=0) ∧ (R^3-A*R^2+B*R-48=0) ∧ (1/P + 2/Q + 3/R = 3/2)) := by
  constructor
  -- prove the inequality --

  -- Firstly, use Vieta theorem to obtain the product --
  . have prod_eq: p * q * r = 48 := by
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

  -- Now, we can use the AM-GM inequality --
    have ineq: (1/p + 2/q + 3/r) ≥ 3 * ((1/p) * (2/q) * (3/r)) ^ ((1:ℝ) /3) := by
      -- we will use the AM-GM inequality to prove this, very carefully --
      have hp1: 0 ≤ 1/p := by
        simp [h_pos]
        linarith
      have hp2: 0 ≤ 2/q := by
        have o: 0 < q := by linarith
        have j: 0 < 2/q := by
          apply div_pos
          norm_num
          exact o
        linarith
      have hp3: 0 ≤ 3/r := by
        have o: 0 < r := by linarith
        have j: 0 < 3/r := by
          apply div_pos
          norm_num
          exact o
        linarith
      have hw0: 0 ≤ ((1:ℝ)/3) := by
        norm_num
      have hw: ((1:ℝ)/3) + ((1:ℝ)/3) + ((1:ℝ)/3) = 1 := by
        norm_num
      have h_am_gm:= Real.geom_mean_le_arith_mean3_weighted hw0 hw0 hw0 hp1 hp2 hp3 hw  -- apply AM-GM --
      let a:= 1/p
      have ha: 1/p = a := by rfl
      rw [ha] at hp1
      let b:= 2/q
      have hb: 2/q = b := by rfl
      rw [hb] at hp2
      let c:= 3/r
      have hc: 3/r = c := by rfl
      rw [hc] at hp3
      simp [ha,hb,hc] at h_am_gm
      simp [ha,hb,hc]
      clear_value a b c
      field_simp
      field_simp at h_am_gm
      have eq1: a ^ ((1:ℝ)/3) * b ^ ((1:ℝ)/3) * c ^ ((1:ℝ)/3) = (a * b * c) ^ ((1:ℝ)/3) := by
        rw [show a ^ ((1:ℝ)/3) * b ^ ((1:ℝ)/3) = (a * b) ^ ((1:ℝ)/3) by rw [Real.mul_rpow hp1 hp2]]
        have s: 0 ≤ a * b := by
          apply mul_nonneg
          apply hp1
          apply hp2
        rw [← Real.mul_rpow s hp3]
      rw [eq1] at h_am_gm
      nlinarith

    -- compute the right side --
    have right_eq: 3 * ((1/p) * (2/q) * (3/r)) ^ ((1:ℝ)/3) = 3 / 2 := by
      field_simp
      rw [prod_eq]
      norm_num
      have id: (1 / 8) ^ ((1:ℝ) / 3) = (1:ℝ) / 2 := by
        rw [show ((1:ℝ) / 3) = 3⁻¹ by norm_num]
        symm
        rw [Real.eq_rpow_inv]
        norm_num
        norm_num
        norm_num
        norm_num
      rw [id]
      norm_num
    rw [right_eq] at ineq
    exact ineq

 -- prove the existence of P, Q, R, A, B --
  . use 2
    use 4
    use 6
    use 12
    use 44
    norm_num