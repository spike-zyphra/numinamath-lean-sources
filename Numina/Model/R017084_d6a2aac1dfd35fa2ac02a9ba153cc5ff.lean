import Mathlib

theorem number_theory_19363 {R C : ℕ} (hR : R * C = 105) (hC : (R + 6) * (C - 2) = 105) :
    R = 15 := by
  have h1 : R ∣ 105 := by
    use C
    all_goals linarith
  have h2 : R ≤ 105 := by
    exact Nat.le_of_dvd (by norm_num) h1
  interval_cases R <;> try { 
    omega 
  } <;> try { 
    omega 
  }