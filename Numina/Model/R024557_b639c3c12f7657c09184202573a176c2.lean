import Mathlib

theorem algebra_322619 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
    x ^ 2 + y ^ 2 = 146 := by 
  have eq3 : x ≤ 35 := by
    by_contra h 
    push_neg at h 
    have h4 : y ≤ 35 := by
      nlinarith 
    interval_cases y <;> try { 
      omega 
    }
  have eq4 : y ≤ 35 := by 
    by_contra h 
    push_neg at h 
    have h5 : x ≤ 35 := by
      nlinarith 
    interval_cases x <;> try { 
      omega 
    }
  interval_cases x <;> interval_cases y <;> omega