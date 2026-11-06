import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312026 (x : Fin 5 → ℝ) (hx : ∀ i, x i ∈ Icc 0 1) :
    x 0 - x 1^3 + x 1 - x 2^3 + x 2 - x 3^3 + x 3 - x 4^3 + x 4 - x 0^3 ≤ 4 := by

  have hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1 := hx 0
  have hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1 := hx 1
  have hx2 : 0 ≤ x 2 ∧ x 2 ≤ 1 := hx 2
  have hx3 : 0 ≤ x 3 ∧ x 3 ≤ 1 := hx 3
  have hx4 : 0 ≤ x 4 ∧ x 4 ≤ 1 := hx 4

  have h01 : 0 ≤ x 0 := hx0.1
  have h02 : x 0 ≤ 1 := hx0.2
  have h11 : 0 ≤ x 1 := hx1.1
  have h12 : x 1 ≤ 1 := hx1.2
  have h21 : 0 ≤ x 2 := hx2.1
  have h22 : x 2 ≤ 1 := hx2.2
  have h31 : 0 ≤ x 3 := hx3.1
  have h32 : x 3 ≤ 1 := hx3.2
  have h41 : 0 ≤ x 4 := hx4.1
  have h42 : x 4 ≤ 1 := hx4.2
  
  nlinarith [sq_nonneg (x 0 - 1 / 2), sq_nonneg (x 1 - 1 / 2), sq_nonneg (x 2 - 1 / 2), sq_nonneg (x 3 - 1 / 2), sq_nonneg (x 4 - 1 / 2),
          sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4), sq_nonneg (x 4 - x 0),
          mul_nonneg (show (0 : ℝ) ≤ x 0 by linarith [h01, h02]) (show (0 : ℝ) ≤ 1 - x 0 by linarith [h01, h02]),
          mul_nonneg (show (0 : ℝ) ≤ x 1 by linarith [h11, h12]) (show (0 : ℝ) ≤ 1 - x 1 by linarith [h11, h12]),
          mul_nonneg (show (0 : ℝ) ≤ x 2 by linarith [h21, h22]) (show (0 : ℝ) ≤ 1 - x 2 by linarith [h21, h22]),
          mul_nonneg (show (0 : ℝ) ≤ x 3 by linarith [h31, h32]) (show (0 : ℝ) ≤ 1 - x 3 by linarith [h31, h32]),
          mul_nonneg (show (0 : ℝ) ≤ x 4 by linarith [h41, h42]) (show (0 : ℝ) ≤ 1 - x 4 by linarith [h41, h42])
          ]