import Mathlib

open Real NNReal Nat BigOperators

/- Prove that $\frac{1}{3} n^{2}+\frac{1}{2} n+\frac{1}{6} \geq(n!)^{2 / n}$ ( $n$ is a positive integer) and that equality is possible only in the case $n=1$. -/
theorem Other_640 {n : PNat} :
  (n ! : ℝ)^((2:ℝ) / n) ≤ (1/3 : ℝ)*n^2 + (1/2 : ℝ)*n + (1/6 : ℝ) ∧
  ((n ! : ℝ)^((2:ℝ) / n) = (1/3 : ℝ)*n^2 + (1/2 : ℝ)*n + (1/6 : ℝ) ↔ n = 1) := by

  -- Unweighted AM-GM, which is mathlib's weighte AM-GM with equal weights
  have amgm_unweighted
    (n : PNat)
    (z : Fin n → ℝ)
    (hz : ∀ i : Fin n, 0 ≤ z i)
  : (∏ i : Fin n, z i) ^ ((1:ℝ)/n) ≤ (1/n) * ∑ i : Fin n, z i := by
    have amgm
      (w z : Fin n → ℝ)
      (hw : ∀ i : Fin n, 0 ≤ w i)
      (hw' : ∑ i : Fin n, w i = 1)
      (hz : ∀ i : Fin n, 0 ≤ z i)
    := by
      exact geom_mean_le_arith_mean_weighted Finset.univ w z (fun i _ => hw i) hw' fun i _ => hz i

    have test'' := amgm (fun _ ↦ 1/n) z (by dsimp; norm_num) (by
      rw [Fin.sum_const]
      field_simp
    ) hz

    dsimp at test''

    rw [←(Finset.mul_sum Finset.univ z (1 / n))] at test''
    rw [Real.finset_prod_rpow Finset.univ z (fun i a => hz i) (1 / n)] at test''

    exact test''

  -- By AM-GM, (1⬝2…n)^(1/n) ≤ (1+2+…n)/n
  have amgm_fact (n : PNat) := amgm_unweighted n (fun i ↦ (i+1)) (by intro x; positivity)
  dsimp at amgm_fact
  specialize amgm_fact n

  -- Rewrite from Fin n to Finset.range n
  rw [←Finset.sum_range (fun i ↦ (i:ℝ) + 1 )] at amgm_fact
  rw [←Finset.prod_range (fun i ↦ (i:ℝ) + 1 )] at amgm_fact

  norm_cast at amgm_fact

  -- Simplify 1⬝2…n = to n!
  rw [Finset.prod_range_add_one_eq_factorial] at amgm_fact

  -- The RHS of amgm_fact is written as ∑ i+1. Split this into ∑i + ∑1, and sum them separately.
  rw [Finset.sum_add_distrib] at amgm_fact

  push_cast at amgm_fact

  -- Closed form for ∑i
  have sum_range_id (n : PNat) : ∑ i ∈ Finset.range n, (i:ℝ) = (n:ℝ) * (n - 1) / 2 := by
    rw [show ∑ i ∈ Finset.range n, (i:ℝ) = ∑ i ∈ Finset.range n, i by push_cast; rfl]
    rw [Finset.sum_range_id]
    field_simp
    norm_cast
    rw [Nat.div_two_mul_two_of_even]
    simp
    exact even_mul_pred_self n

  rw [sum_range_id] at amgm_fact

  -- Closed form for ∑1
  have sum_range_one : ∑ x ∈ Finset.range n, (1:ℝ) = (n:ℕ) := by
    norm_cast
    rw [Finset.sum_range_induction (fun k => 1) (fun {n} => n) rfl (congrFun rfl) n]

  rw [sum_range_one] at amgm_fact

  field_simp at amgm_fact

  -- After substituting the closed forms, we can cancel the n
  rw [show ((n:ℝ) * (n - 1) + n * 2) / (n * 2) = (n + 1) / 2 by field_simp; ring] at amgm_fact

  -- (n!)^(2/n) ≤ (n+1)(n+1)/4
  have fac_le_quad := calc
    ((n !):ℝ)^((2:ℝ) / n) = ((n !)^((1:ℝ) / n))^(2:ℝ) := by
      rw [←Real.rpow_mul]
      congr
      ring
      positivity
    _ ≤ (((n:ℝ)+1)/2)^(2:ℝ) := by
      gcongr -- amgm_fact implicitly used here
    _ = ((n:ℝ)+1)*((n+1)/4) := by
      norm_cast
      ring

  -- The main inequality, (n!)^(2/n) ≤ n^2/3 + n/2 + 1/6, which is `fac_le_quad` with a simple estimate of two polynomials
  have main := calc
    ((n !):ℝ)^((2:ℝ) / n) ≤ ((n:ℝ)+1)*((n+1)/4) := fac_le_quad
    _ ≤ ((n:ℝ)+1)*((2*n+1)/6) := by
      gcongr _ * ?_
      have : ((n:ℝ) + 1) * 6 ≤ (2 * n + 1) * 4 := by
        have : (1:ℝ) ≤ n := by
          norm_cast
          exact PNat.one_le n
        linarith
      linarith
    _ = 1 / 3 * n ^ 2 + 1 / 2 * n + 1 / 6 := by ring

  constructor
  · exact main

  constructor

  -- In the equality case, each inequality in `main` must secretly be an equality; however with 1 < n, one of the steps is a strict inequality. We proceed by contradiction.

  intro heq

  by_contra h

  have n_gt_1 : 1 < n := lt_of_le_of_ne (PNat.one_le n) fun a => h (Eq.symm a)

  -- With 1 < n, the chain of inequalities contains one strict inequality
  have : ((n !):ℝ)^((2:ℝ) / n) <  1 / 3 * n ^ 2 + 1 / 2 * n + 1 / 6 := by
    calc
    ((n !):ℝ)^((2:ℝ) / n) ≤ ((n:ℝ)+1)*((n+1)/4) := fac_le_quad
    _ < ((n:ℝ)+1)*((2*n+1)/6) := by
      gcongr _ * ?_
      have : ((n:ℝ) + 1) * 6 < (2 * n + 1) * 4 := by
        have : (1:ℝ) < n := by
          norm_cast
        linarith
      linarith
    _ = 1 / 3 * n ^ 2 + 1 / 2 * n + 1 / 6 := by ring

  -- We have A < B and A = B, which is a contradiction
  linarith

  -- The other direction is a straightforward computation
  intro n_eq_1
  rw [n_eq_1]
  norm_num
