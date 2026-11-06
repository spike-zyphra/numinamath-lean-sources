import Mathlib

theorem algebra_258765 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hsum : x^2 + y^2 = 208) (hprod : x * y = 96) :
    x = 8 ∧ y = 12 ∨ x = 12 ∧ y = 8 := by
  have h1 : x ≤ 32 := by
    by_contra h
    push_neg at h
    have h2 : y ≤ 2 := by
      nlinarith [show x ≥ 33 by linarith, hprod]
    interval_cases y <;> try { 
      omega 
    }
    all_goals
      try { 
        nlinarith 
      }
  -- Similarly for y, the same bound can be proved
  have h2 : y ≤ 32 := by
    by_contra h
    push_neg at h
    have h3 : x ≤ 2 := by
      nlinarith [show y ≥ 33 by linarith, hprod]
    interval_cases x <;> try { 
      omega 
    }
    all_goals
      try { 
        nlinarith 
      }
  -- Now both x and y are bounded, so we can check all possible cases
  interval_cases x <;> try { 
    omega 
  }
  <;> interval_cases y
  <;> omega