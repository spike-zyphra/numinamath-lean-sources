import Mathlib

theorem algebra_107028 {X Y : ℤ} (hX : X > 0) (hY : Y > 0)
    (h : (5 + 1 / X : ℚ) * (Y + 1 / 2) = 43) :
    X = 17 ∧ Y = 8 := by
  have h1 : (X : ℚ) > 0 := by exact_mod_cast hX
  have h2 : (Y : ℚ) > 0 := by exact_mod_cast hY
  have eq1 : (5 + 1 / X : ℚ) * (Y + 1 / 2) = 43 := by linarith
  have eq2 : (5 * X + 1 : ℚ) * (2 * Y + 1) = 86 * (X : ℚ) := by
    field_simp at eq1 ⊢
    nlinarith
  have eq3 : (5 * X + 1 : ℤ) * (2 * Y + 1) = 86 * X := by
    exact_mod_cast eq2
  have h3 : Y ≤ 8 := by
    nlinarith [show 5 * X + 1 ≥ 6 from by nlinarith, 
      show 2 * Y + 1 ≥ 3 from by nlinarith]
  interval_cases Y <;> 
    try { 
      omega
    }
    <;> 
    try { 
      have h4 : X ≤ 43 := by
        nlinarith
      interval_cases X <;> 
        try { 
          omega 
        }
    }
    <;> 
    nlinarith