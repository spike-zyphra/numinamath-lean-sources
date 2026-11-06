import Mathlib

theorem algebra_112857 (x y z : ℕ) (hx : 10 ≤ x ∧ x < 100) (hy : 10 ≤ y ∧ y < 100)
    (hz : 10 ≤ z ∧ z < 100) (h : (x + y + z) / 3 = 60) :
    (x + y) / z ≤ 17 := by
  have h1 : x ≥ 10 := hx.1
  have h2 : x < 100 := hx.2
  have h3 : y ≥ 10 := hy.1
  have h4 : y < 100 := hy.2
  have h5 : z ≥ 10 := hz.1
  have h6 : z < 100 := hz.2
  have h7 : x + y + z ≥ 180 := by 
    omega
  have h8 : x + y + z < 183 := by 
    omega
  interval_cases z <;> try { 
    omega 
  } <;> try { 
    all_goals try { 
      omega 
    }
  }
  all_goals try { 
    omega 
  }
  all_goals try { 
    omega 
  }
  all_goals try { 
    omega 
  }
  all_goals try { 
    omega 
  }
  all_goals try { 
    omega 
  }
  all_goals try { 
    omega 
  }