import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_120426 (f : ℝ → ℝ) (hf : f = λ x => 2^x + 3^(-x) + 4^(-x) + 6^x) :
    ∀ x, f x ≥ 4 ∧ (f x = 4 ↔ x = 0) := by
  intro x
  have hfx1 : f x = (2 : ℝ) ^ x + (3 : ℝ) ^ (-x) + (4 : ℝ) ^ (-x) + (6 : ℝ) ^ x := by
    rw [hf]
    all_goals norm_num
    <;> ring_nf
  constructor
  · -- First part: show that $f(x) \geq 4$ for all $x \in \mathbb{R}$.
    rw [hfx1]
    have h5 : (2 : ℝ) ^ x + (3 : ℝ) ^ (-x) + (4 : ℝ) ^ (-x) + (6 : ℝ) ^ x - 4 ≥ 0 := by
      have h5_prod_eq1 : (2 : ℝ) ^ x * (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) * (6 : ℝ) ^ x = 1 := by
        have h1 : (2 : ℝ) ^ x * (6 : ℝ) ^ x = (12 : ℝ) ^ x := by
          calc
            (2 : ℝ) ^ x * (6 : ℝ) ^ x = ((2 * 6) : ℝ) ^ x := by rw [Real.mul_rpow]; all_goals linarith
            _ = (12 : ℝ) ^ x := by norm_num
        have h2 : (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) = (12 : ℝ) ^ (-x) := by
          calc
            (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) = ((3 * 4) : ℝ) ^ (-x) := by rw [Real.mul_rpow]; all_goals linarith
            _ = (12 : ℝ) ^ (-x) := by norm_num
        calc
          (2 : ℝ) ^ x * (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) * (6 : ℝ) ^ x
              = ((2 : ℝ) ^ x * (6 : ℝ) ^ x) * ((3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x)) := by ring
          _ = ((12 : ℝ) ^ x) * ((12 : ℝ) ^ (-x)) := by rw [h1, h2]
          _ = ((12 : ℝ) ^ x * (12 : ℝ) ^ (-x)) := by ring
          _ = (12 : ℝ) ^ (x + (-x)) := by rw [Real.rpow_add]; all_goals linarith
          _ = (12 : ℝ) ^ (0 : ℝ) := by rw [add_right_neg]
          _ = 1 := by simp
      have h6_pos1 : (2 : ℝ) ^ x > 0 := by positivity
      have h6_pos2 : (3 : ℝ) ^ (-x) > 0 := by positivity
      have h6_pos3 : (4 : ℝ) ^ (-x) > 0 := by positivity
      have h6_pos4 : (6 : ℝ) ^ x > 0 := by positivity
      nlinarith [sq_nonneg ((2 : ℝ) ^ x - 1), sq_nonneg ((3 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((4 : ℝ) ^ (-x) - 1), sq_nonneg ((6 : ℝ) ^ x - 1),
            sq_nonneg ((2 : ℝ) ^ x * (3 : ℝ) ^ (-x) - 1), sq_nonneg ((2 : ℝ) ^ x * (4 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((2 : ℝ) ^ x * (6 : ℝ) ^ x - 1), sq_nonneg ((3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((3 : ℝ) ^ (-x) * (6 : ℝ) ^ x - 1), sq_nonneg ((4 : ℝ) ^ (-x) * (6 : ℝ) ^ x - 1), 
            h5_prod_eq1, 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (3 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (4 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (6 : ℝ) ^ x by positivity), 
            mul_pos (show 0 < (3 : ℝ) ^ (-x) by positivity) (show 0 < (4 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (3 : ℝ) ^ (-x) by positivity) (show 0 < (6 : ℝ) ^ x by positivity), 
            mul_pos (show 0 < (4 : ℝ) ^ (-x) by positivity) (show 0 < (6 : ℝ) ^ x by positivity)
            ]
    linarith
  · -- Now, we need to prove that f x = 4 iff x = 0
    rw [hfx1]
    constructor
    · -- If f x = 4, then x = 0
      intro h_eq
      have h5_prod_eq1 : (2 : ℝ) ^ x * (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) * (6 : ℝ) ^ x = 1 := by
        have h1 : (2 : ℝ) ^ x * (6 : ℝ) ^ x = (12 : ℝ) ^ x := by
          calc
            (2 : ℝ) ^ x * (6 : ℝ) ^ x = ((2 * 6) : ℝ) ^ x := by rw [Real.mul_rpow]; all_goals linarith
            _ = (12 : ℝ) ^ x := by norm_num
        have h2 : (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) = (12 : ℝ) ^ (-x) := by
          calc
            (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) = ((3 * 4) : ℝ) ^ (-x) := by rw [Real.mul_rpow]; all_goals linarith
            _ = (12 : ℝ) ^ (-x) := by norm_num
        calc
          (2 : ℝ) ^ x * (3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) * (6 : ℝ) ^ x
              = ((2 : ℝ) ^ x * (6 : ℝ) ^ x) * ((3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x)) := by ring
          _ = ((12 : ℝ) ^ x) * ((12 : ℝ) ^ (-x)) := by rw [h1, h2]
          _ = ((12 : ℝ) ^ x * (12 : ℝ) ^ (-x)) := by ring
          _ = (12 : ℝ) ^ (x + (-x)) := by rw [Real.rpow_add]; all_goals linarith
          _ = (12 : ℝ) ^ (0 : ℝ) := by rw [add_right_neg]
          _ = 1 := by simp
      have h6_pos1 : (2 : ℝ) ^ x > 0 := by positivity
      have h6_pos2 : (3 : ℝ) ^ (-x) > 0 := by positivity
      have h6_pos3 : (4 : ℝ) ^ (-x) > 0 := by positivity
      have h6_pos4 : (6 : ℝ) ^ x > 0 := by positivity
      have h10 : (2 : ℝ) ^ x = 1 := by
        nlinarith [sq_nonneg ((2 : ℝ) ^ x - 1), sq_nonneg ((3 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((4 : ℝ) ^ (-x) - 1), sq_nonneg ((6 : ℝ) ^ x - 1),
            sq_nonneg ((2 : ℝ) ^ x * (3 : ℝ) ^ (-x) - 1), sq_nonneg ((2 : ℝ) ^ x * (4 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((2 : ℝ) ^ x * (6 : ℝ) ^ x - 1), sq_nonneg ((3 : ℝ) ^ (-x) * (4 : ℝ) ^ (-x) - 1), 
            sq_nonneg ((3 : ℝ) ^ (-x) * (6 : ℝ) ^ x - 1), sq_nonneg ((4 : ℝ) ^ (-x) * (6 : ℝ) ^ x - 1), 
            h5_prod_eq1, h_eq, 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (3 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (4 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (2 : ℝ) ^ x by positivity) (show 0 < (6 : ℝ) ^ x by positivity), 
            mul_pos (show 0 < (3 : ℝ) ^ (-x) by positivity) (show 0 < (4 : ℝ) ^ (-x) by positivity), 
            mul_pos (show 0 < (3 : ℝ) ^ (-x) by positivity) (show 0 < (6 : ℝ) ^ x by positivity), 
            mul_pos (show 0 < (4 : ℝ) ^ (-x) by positivity) (show 0 < (6 : ℝ) ^ x by positivity)
            ]
      have hx : x = (0 : ℝ) := by
        have h11 : (2 : ℝ) ^ x = 1 := h10
        have h12 : x = (Real.logb (2 : ℝ) (1 : ℝ)) := by
          rw [←h11]
          field_simp
        rw [h12]
        norm_num
        all_goals linarith
        all_goals linarith
      linarith
    · -- If x = 0, then f x = 4
      intro h_eq
      rw [h_eq]
      norm_num