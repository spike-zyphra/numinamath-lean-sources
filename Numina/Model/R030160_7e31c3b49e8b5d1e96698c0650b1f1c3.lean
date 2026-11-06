import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189378 (a b c : ℝ) (h : ∀ x ∈ Icc (-1) 1, |a * x ^ 2 - b * x + c| < 1) :
  ∀ x ∈ Icc (-1) 1, |(a + b) * x ^ 2 + c| < 1 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : |a * x ^ 2 - b * x + c| < 1 := h x ⟨by linarith, by linarith⟩
  have h2 : -1 < a * x ^ 2 - b * x + c := by
    linarith [abs_lt.mp h1]
  have h3 : a * x ^ 2 - b * x + c < 1 := by
    linarith [abs_lt.mp h1]
  have h11 := h (-x) (show (-x) ∈ Icc (-1 : ℝ) 1 by
    constructor <;> linarith 
  )
  have h4 : -1 < a * (-x) ^ 2 - b * (-x) + c := by 
    linarith [abs_lt.mp h11]
  have h5 : a * (-x) ^ 2 - b * (-x) + c < 1 := by 
    linarith [abs_lt.mp h11]
  -- From hypothesis at x = 0 
  have h6 : -1 < c := by
    have h0 := h (0 : ℝ) (by constructor <;> norm_num)
    linarith [abs_lt.mp h0]
  have h7 : c < 1 := by
    have h0 := h (0 : ℝ) (by constructor <;> norm_num)
    linarith [abs_lt.mp h0]
  -- From hypothesis at x=1 and x=-1
  have h8 : -1 < a - b + c := by
    have h11 := h 1 (by norm_num)
    linarith [abs_lt.mp h11]
  have h9 : a - b + c < 1 := by
    have h11 := h 1 (by norm_num)
    linarith [abs_lt.mp h11]
  have h10 : -1 < a + b + c := by
    have h12 := h (-1) (by norm_num)
    linarith [abs_lt.mp h12]
  have h11 : a + b + c < 1 := by
    have h12 := h (-1) (by norm_num)
    linarith [abs_lt.mp h12]
  -- Prove the target bounds using all these inequalities
  have h7 : -1 < (a + b) * x ^ 2 + c := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg ((a + b) * x), sq_nonneg (c - a), sq_nonneg (c - b), 
      mul_nonneg (show 0 ≤ (1 : ℝ) - x by linarith) 
      (show 0 ≤ x + 1 by linarith), 
      sq_nonneg ((x) ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)
      ]
  have h8 : (a + b) * x ^ 2 + c < 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg ((a + b) * x), sq_nonneg (c - a), sq_nonneg (c - b), 
      mul_nonneg (show 0 ≤ (1 : ℝ) - x by linarith) 
      (show 0 ≤ x + 1 by linarith), 
      sq_nonneg ((x) ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)
      ]
  -- Use the previous results to conclude the final inequality using abs_lt.
  have h9 : |(a + b) * x ^ 2 + c| < 1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  exact h9