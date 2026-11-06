import Mathlib

theorem algebra_290633 {a b : ℕ} (h : ∃ x y, x ≠ y ∧ x^2 + a * x + b + 1 = 0 ∧ y^2 + a * y + b + 1 = 0) :
    ¬Prime (a^2 + b^2) := by
  rcases h with ⟨x, y, hxy, hx, hy⟩
  all_goals
    have h1 : x ≥ 0 := by
      linarith
    have h2 : y ≥ 0 := by
      linarith
    -- equation (x+1)^2 + (a*x) + b = 0, contradicts 
    -- x^2 ≥ 0 
    -- equation (x+1)^2 + (a*x) + b = 0, contradicts 
    -- x^2 + 1 ≥ 1
    -- So contradiction.
    have h3 : x^2 + a * x + b + 1 ≥ 1 := by
      have h4 : x^2 ≥ 0 := by
        nlinarith
      have h5 : a * x ≥ 0 := by
        nlinarith
      have h6 : b ≥ 0 := by
        nlinarith
      nlinarith
    -- hx: x^2 +a*x +b +1 =0 contradicts with h3: x^2 +a*x +b +1 ≥1
    linarith