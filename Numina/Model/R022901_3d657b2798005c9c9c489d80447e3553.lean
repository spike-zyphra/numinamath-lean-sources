import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_231412 {f : ℝ → ℝ} (hf : f = λ x => 2 * x ^ 2 - 1) :
    {x | f (f x) < (f x) ^ 2} = {x | x ∈ Ioo (-1) 0 ∨ x ∈ Ioo 0 1} := by
  ext x
  simp only [hf, Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_setOf_eq]
  constructor
  · -- Assume f(f(x)) < (f(x))^2, prove x ∈ (-1,0) ∪ (0,1)
    intro h
    have h1 : (2 * (2 * x ^ 2 - 1) ^ 2 - 1) < (2 * x ^ 2 - 1) ^ 2 := by 
      simpa using h
    have h2 : (2 * x ^ 2 - 1) ^ 2 < 1 := by
      nlinarith 
    have h3 : -1 < 2 * x ^ 2 - 1 := by 
      nlinarith [sq_nonneg (2 * x ^ 2 - 1), h2 ]
    have h4 : 2 * x ^ 2 - 1 < 1 := by 
      nlinarith [sq_nonneg (2 * x ^ 2 - 1), h2 ]
    have h5 : 0 < x ^ 2 := by 
      nlinarith 
    have h6 : -1 < x := by 
      nlinarith [sq_nonneg x, h5, h4] 
    have h7 : x < 1 := by 
      nlinarith [sq_nonneg x, h5, h4] 
    by_cases h8 : x < 0
    · -- x < 0, so x ∈ (-1, 0)
      left
      constructor <;> nlinarith 
    · -- x ≥ 0
      have h8 : 0 ≤ x := by 
        linarith 
      have h9 : 0 < x := by 
        nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by 
          by_contra h0 
          have : x = 0 := by linarith 
          rw [this] at h5 
          nlinarith 
        ), sq_nonneg x]
      right
      constructor <;> nlinarith 
  · -- Assume x ∈ (-1,0) ∪ (0,1), prove f(f(x)) < (f x) ^ 2
    rintro (h | h)
    · -- x ∈ (-1, 0)
      have h1 : -1 < x := by 
        linarith [h.1] 
      have h2 : x < 0 := by 
        linarith [h.2] 
      have h3 : 0 < x ^ 2 := by
        nlinarith 
      have h4 : -1 < 2 * x ^ 2 - 1 := by 
        nlinarith 
      have h5 : 2 * x ^ 2 - 1 < 1 := by 
        nlinarith 
      have h6 : (2 * x ^ 2 - 1) ^ 2 < 1 := by 
        nlinarith [sq_nonneg (x ^ 2), h4, h5] 
      have h7 : (2 * (2 * x ^ 2 - 1) ^ 2 - 1) < (2 * x ^ 2 - 1) ^ 2 := by
        nlinarith [h6] 
      simpa using h7 
    · -- x ∈ (0, 1)
      have h1 : 0 < x := by 
        linarith [h.1] 
      have h2 : x < 1 := by 
        linarith [h.2] 
      have h3 : 0 < x ^ 2 := by 
        nlinarith 
      have h4 : -1 < 2 * x ^ 2 - 1 := by 
        nlinarith 
      have h5 : 2 * x ^ 2 - 1 < 1 := by 
        nlinarith 
      have h6 : (2 * x ^ 2 - 1) ^ 2 < 1 := by 
        nlinarith [sq_nonneg (x ^ 2), h4, h5] 
      have h7 : (2 * (2 * x ^ 2 - 1) ^ 2 - 1) < (2 * x ^ 2 - 1) ^ 2 := by 
        nlinarith [h6] 
      simpa using h7