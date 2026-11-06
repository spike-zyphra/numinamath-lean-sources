import Mathlib

theorem inequalities_2881 (a b c : ℝ) :
    (a - b) ^ 3 * (b - c) ^ 3 + (b - c) ^ 3 * (c - a) ^ 3 + (c - a) ^ 3 * (a - b) ^ 3 ≤
    3 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 := by 
        nlinarith [sq_nonneg ((a - b) * (b - c) * (c - a)), 
          sq_nonneg ((a - b) * (b - c) + (b - c) * (c - a) + (c - a) * (a - b)), 
          sq_nonneg ((a - b) ^ 2 * (b - c) ^ 2 + (b - c) ^ 2 * (c - a) ^ 2 + (c - a) ^ 2 * (a - b) ^ 2), 
          sq_nonneg ( (a - b) * (b - c) * (b - c) * (c - a) ), 
          sq_nonneg ( (a - b) * (b - c) * (c - a) ), 
          sq_nonneg ( (b - c) * (c - a) * (a - b) ), 
          sq_nonneg ( (a - b) * (b - c) + (b - c) * (c - a) + (c - a) * (a - b) ), 
          sq_nonneg ( (a - b) + (b - c) + (c - a) ), 
          sq_nonneg ( (a - b) * (b - c) ), 
          sq_nonneg ( (b - c) * (c - a) ), 
          sq_nonneg ( (c - a) * (a - b) ), 
          sq_nonneg ( (a - b) * (b - c) * (c - a) ) ]