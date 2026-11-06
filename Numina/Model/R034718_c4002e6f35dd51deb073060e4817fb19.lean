import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_312683 (a : ℝ) :
  (∀ x ∈ Icc (-2) (1/2), a * x^3 - x^2 + x + 1 ≥ 0) ↔
  -10 ≤ a ∧ a ≤ -1 := by 
  constructor
  · -- Assume inequality holds, prove bounds.
    intro h
    have h1 := h (-2) (by norm_num)
    have h2 := h (1/2) (by norm_num)
    have h3 := h 0 (by norm_num)
    have h4 := h (-1) (by norm_num)
    have h5 : a ≤ -1 := by 
      nlinarith 
    have h6 : -10 ≤ a := by
      norm_num at h2 
      nlinarith 
    constructor 
    · linarith 
    · linarith 
  · -- Assume bounds, prove inequality.
    rintro ⟨ha1, ha2⟩ 
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    by_cases h9 : x ≥ 0
    · -- Case x ≥ 0
      have h11 : x ≥ 0 := h9
      have h12 : x ≤ 1/2 := by linarith 
      have h13 : a * x ^ 3 - x^2 + x + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg ((x * a) + x / 2), sq_nonneg (x * (x * a)), 
            sq_nonneg ((x - 1/2) * x * a), sq_nonneg ((x -1) *x *a),
            mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - 2 * x by nlinarith),
            mul_nonneg (show (0 : ℝ) ≤ 2 * x by nlinarith) (show (0 : ℝ) ≤ 1 - 2 * x by nlinarith),
            sq_nonneg (a), sq_nonneg (x * a), sq_nonneg ((x + 1) * x * a), sq_nonneg ((x + 1) * (x^2)), sq_nonneg (x * (x -1/2)), sq_nonneg ((x * a) -x ^ 2), sq_nonneg ((x * a) *x^2), sq_nonneg ((a + 10)), sq_nonneg ((a)*x^2), sq_nonneg ((a)*x)
        ]
      linarith 
    · -- Case x < 0 
      push_neg at h9
      have h11 : x < (0 : ℝ) := h9 
      have h13 : a * x ^ 3 - x^2 + x + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x +1), sq_nonneg ((x +1) * (x +1)), 
          mul_nonneg (show (0 : ℝ) ≤ x + 2 by nlinarith) (show (0 : ℝ) ≤ 1 - x by nlinarith), 
          sq_nonneg (x * (x)), sq_nonneg ((x ^ 2) / 2), sq_nonneg ((x *a) * (x^2)), sq_nonneg (x^2), 
          sq_nonneg ((x * a) *x^2), sq_nonneg ( (a + 10) * x^2 ), sq_nonneg ( (a + 1) * x^2 ) 
          ]
      linarith