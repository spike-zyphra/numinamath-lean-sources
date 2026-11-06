import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_221160 (P : ℝ × ℝ) (hP : P = (3, 4)) :
    IsLeast {d | ∃ x y, d = sqrt ((x - P.1)^2 + (y - P.2)^2) ∧
      y * (x^2 + y^2) - x * (x^2 + y^2) - y + x = 0} (sqrt ((3.5 - P.1)^2 + (3.5 - P.2)^2)) := by 
  rw [hP]
  constructor
  · -- Show sqrt ((3.5 - (3 : ℝ)) ^ 2 + (3.5 - (4 : ℝ)) ^ 2) is in the set.
    use 3.5, 3.5
    constructor
    · -- Show that the distance is equal
      norm_num
    · -- Show that the point satisfies the equation
      norm_num
  · -- Show it is minimal
    intro d hd
    rcases hd with ⟨x, y, hd_eq, heq⟩
    have h_eq : y * (x ^ 2 + y ^ 2) - x * (x ^ 2 + y ^ 2) - y + x = 0 := heq
    have h_eq' : (y - x) * (x ^ 2 + y ^ 2 - 1) = 0 := by
      ring_nf at h_eq ⊢
      nlinarith
    have h1 : y - x = 0 ∨ x ^ 2 + y ^ 2 - 1 = 0 := by 
      cases (mul_eq_zero.mp h_eq') with
      | inl h2 => left; linarith
      | inr h3 => right; linarith
    cases h1 with 
    | inl h => -- Assume y - x = 0, so y = x
      have hy : y = x := by linarith
      rw [hy] at hd_eq
      have h3 : (x - 3) ^ 2 + (x - 4) ^ 2 ≥ (3.5 - (3 : ℝ)) ^ 2 + (3.5 - (4 : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (x - 3.5)]
      have h4 : sqrt ((x - (3 : ℝ)) ^ 2 + (x - (4 : ℝ)) ^ 2) ≥ sqrt ((3.5 - (3 : ℝ)) ^ 2 + (3.5 - (4 : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by linarith [h3])
      linarith [h4, hd_eq]
    | inr h2 => 
      -- Assume x ^ 2 + y ^ 2 - 1 = 0
      have h7 : x ^ 2 + y ^ 2 = 1 := by linarith
      have h8 : (x - 3) ^ 2 + (y - 4) ^ 2 ≥ (3.5 - (3 : ℝ)) ^ 2 + (3.5 - (4 : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (x - 3.5), sq_nonneg (y - 3.5),
          h7, 
          sq_nonneg (x - y)
        ]
      have h4 : sqrt ((x - (3 : ℝ)) ^ 2 + (y - (4 : ℝ)) ^ 2) ≥ sqrt ((3.5 - (3 : ℝ)) ^ 2 + (3.5 - (4 : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by linarith [h8])
      linarith [h4, hd_eq]