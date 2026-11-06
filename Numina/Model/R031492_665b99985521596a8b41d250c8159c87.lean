import Mathlib

open Real MeasureTheory

theorem calculus_99850 (a x : ℝ) :
    ∃ c, ∫ x in a..x, x * log (1 + √(1 + x ^ 2)) / √(1 + x ^ 2) =
      (1 + √(1 + x ^ 2)) * log (1 + √(1 + x ^ 2)) - √(1 + x ^ 2) + c := by
  set c := (∫ x in a..x, x * log (1 + √(1 + x ^ 2)) / √(1 + x ^ 2) ) - ( (1 + √(1 + x ^ 2)) * log (1 + √(1 + x ^ 2)) - √(1 + x ^ 2) ) with hc
  use c
  all_goals
  try { 
    simp only [hc]
    all_goals 
      try { 
        linarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + a ^ 2), sq_nonneg (x - a), Real.sqrt_nonneg (1 + 0 ^ 2)]
      }
    all_goals try { 
      nlinarith [sq_nonneg (x - a), sq_nonneg (x + a), sq_nonneg (x - 0), sq_nonneg (a - 0), Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + 0 ^ 2) ]
    }
  }
  all_goals try { tauto }
  all_goals try { 
    ring_nf <;> try { 
      simp [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + a ^ 2)]
    }
    <;> try { 
      nlinarith [sq_nonneg (x - a), sq_nonneg (x + a), sq_nonneg (x - 0), sq_nonneg (a - 0) ]
    }
  }
  all_goals try { tauto }
  all_goals try { 
    linarith 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { nlinarith [sq_nonneg (x - a), sq_nonneg (x + a)] }
  all_goals try { nlinarith }