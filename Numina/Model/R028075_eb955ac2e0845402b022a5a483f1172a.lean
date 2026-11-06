import Mathlib
theorem algebra_15792 {x : ℕ} (hx : 2 ∣ x ∧ 3 ∣ x ∧ 6 ∣ x)
    (h : (x / 3) + (2 / 3 * (1 / 4) * x) + (15:ℚ) + 15 + 1 + 3 ≤ x ∧ x ≤ (x / 3) + (2 / 3 * (1 / 4) * x) +(15:ℚ) + 15 + 5 + 3) :
    x = 72 := by 
  have h1 := h.1
  have h2 := h.2
  have h3 : (68 : ℚ) ≤ (x : ℚ) := by
    linarith
  have h4 : (x : ℚ) ≤ (76 : ℚ) := by
    linarith 
  have h5 : 68 ≤ x := by
    exact_mod_cast h3
  have h6 : x ≤ 76 := by 
    exact_mod_cast h4
  -- We need to use that x is multiple of 6, which is the 3rd part of hx
  have h7 : x % 6 = 0 := by 
    omega 
  -- Finally, omega should determine x from the constraints
  omega 
  all_goals try linarith