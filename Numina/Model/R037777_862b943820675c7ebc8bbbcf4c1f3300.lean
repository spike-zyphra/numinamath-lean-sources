import Mathlib

open Real

theorem inequalities_95040 :
IsGreatest {y | ∃ t : Fin 6 → ℝ,
(∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) ∧ t 0 * t 2 * t 4 + t 1 * t 3 * t 5 ≥ 1 / 540 ∧
y = t 0 * t 1 * t 2 + t 1 * t 2 * t 3 + t 2 * t 3 * t 4 + t 3 * t 4 * t 5 + t 4 * t 5 * t 0 + t 5 * t 0 * t 1} (19 / 540) := by 
  rw [IsGreatest, upperBounds]
  constructor
  · -- Let's show 19/540 is achievable
    use λ i =>
      match i with
      | ⟨0, _⟩ => 1/3
      | ⟨1, _⟩ => 19/60
      | ⟨2, _⟩ => 1/3
      | ⟨3, _⟩ => 0
      | ⟨4, _⟩ => 1/60
      | ⟨5, _⟩ => 0
    constructor
    · intro i
      fin_cases i <;> norm_num
    constructor
    · simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      norm_num
    constructor
    · norm_num
    · norm_num
  · -- Let's show 19/540 is the greatest upper bound
    simp
    intro a x hx₁ hx₂ hx₃ ha
    have h1 : (x 0 * x 1 * x 2 + x 1 * x 2 * x 3 + x 2 * x 3 * x 4 + x 3 * x 4 * x 5 + x 4 * x 5 * x 0 + x 5 * x 0 * x 1) ≤ 19 / 540 := by
      have hx0 : 0 ≤ x 0 := hx₁ 0
      have hx1 : 0 ≤ x 1 := hx₁ 1
      have hx2 : 0 ≤ x 2 := hx₁ 2
      have hx3 : 0 ≤ x 3 := hx₁ 3
      have hx4 : 0 ≤ x 4 := hx₁ 4
      have hx5 : 0 ≤ x 5 := hx₁ 5
      have ineq : (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) ≤ (1 / 27: ℝ) := by
        have h1 : (x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) = 1 := by
          have h2 : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 = 1 := by
            simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx₂ ⊢
            linarith
          linarith
        have h2 : (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) ≤ ((x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5)) ^ 3 / 27 := by
          nlinarith [sq_nonneg ((x 0 + x 3) - (x 1 + x 4)), sq_nonneg ((x 0 + x 3) - (x 2 + x 5)), sq_nonneg ((x 1 + x 4) - (x 2 + x 5)), 
            mul_nonneg (show 0 ≤ x 0 + x 3 by linarith) (show 0 ≤ x 1 + x 4 by linarith), 
            mul_nonneg (show 0 ≤ x 1 + x 4 by linarith) (show 0 ≤ x 2 + x 5 by linarith), 
            mul_nonneg (show 0 ≤ x 0 + x 3 by linarith) (show 0 ≤ x 2 + x 5 by linarith)
          ]
        have h3 : ((x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5)) ^ 3 ≤ (1: ℝ) := by
          have h10 : (x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) = 1 := h1
          have h4 : ((x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5)) ^ 3 ≤ (1: ℝ) := by
            have h5 : 0 ≤ (x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) := by linarith
            have h6 : (x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) ≤ 1 := by linarith
            nlinarith [sq_nonneg ((x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) - 1), sq_nonneg ((x 0 + x 3) + (x 1 + x 4) + (x 2 + x 5) - 1)]
          linarith
        have h4 : (x 0 + x 3) * (x 1 + x 4) * (x 2 + x 5) ≤ (1 / 27: ℝ) := by
          nlinarith
        linarith
      have ineq2 : x 0 * x 1 * x 2 + x 1 * x 2 * x 3 + x 2 * x 3 * x 4 + x 3 * x 4 * x 5 + x 4 * x 5 * x 0 + x 5 * x 0 * x 1 ≤ 19 / 540 := by
        nlinarith [sq_nonneg (x 0 - 1 / 3), sq_nonneg (x 1 - 19 / 60), sq_nonneg (x 2 - 1 / 3), 
          sq_nonneg (x 3), sq_nonneg (x 4 - 1 / 60), sq_nonneg (x 5), 
          mul_nonneg hx0 hx1, mul_nonneg hx1 hx2, mul_nonneg hx2 hx3, 
          mul_nonneg hx3 hx4, mul_nonneg hx4 hx5, mul_nonneg hx5 hx0, 
          hx₃
        ]
      linarith
    linarith [h1, ha]