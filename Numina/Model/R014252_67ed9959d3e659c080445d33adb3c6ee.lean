import Mathlib

theorem inequalities_7207 (r y b : ℕ)
    (h₀ : b ≤ (1 / 3 : ℚ) * y)
    (h₁ : b ≥ (1 / 2 : ℚ) * r)
    (h₂ : y + b ≤ 73) :
    r ≤ 36 := by

  have h0 : (3 * (b : ℚ) ) ≤ (y : ℚ) := by 
    linarith

  have h0' : 3 * b ≤ y := by 
    exact_mod_cast h0

  -- Convert h₁ from rational to integer inequality.
  have h1 : (2 * (b : ℚ)) ≥ (r : ℚ) := by
    linarith

  -- Convert h1 to integer inequality.
  have h1' : 2 * b ≥ r := by 
    exact_mod_cast h1

  have h3 : b ≤ 18 := by 
    omega -- automatically derives from h0' and h₂

  -- Using h3 and h1', we can derive r ≤ 36.
  have h4 : r ≤ 36 := by 
    omega -- automatically derives from h1' and h3

  exact h4