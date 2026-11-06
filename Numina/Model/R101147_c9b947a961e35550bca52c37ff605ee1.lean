import Mathlib

theorem inequalities_602059 (x y z : ℝ) :
    abs x + abs y + abs z ≤ abs (x + y - z) + abs (x - y + z) + abs (-x + y + z) := by 
  cases' abs_cases x with hx hx
  · cases' abs_cases y with hy hy
    · cases' abs_cases z with hz hz
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where all expressions are non-negative
              nlinarith
            · -- Case where -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where -x + y + z ≥ 0 and x - y + z < 0
              nlinarith
            · -- Case where both -x + y + z < 0 and x - y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where all expressions are negative
              nlinarith
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where z < 0 and all expressions are non-negative
              nlinarith
            · -- Case where z < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where z < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where z < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where z < 0 and all expressions are negative
              nlinarith
    · cases' abs_cases z with hz hz
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0 and all expressions are non-negative
              nlinarith
            · -- Case where y < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0 and all expressions are negative
              nlinarith
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, z < 0 and all expressions are non-negative
              nlinarith
            · -- Case where y < 0, z < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0, z < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where y < 0, z < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where y < 0, z < 0 and all expressions are negative
              nlinarith
  · cases' abs_cases y with hy hy
    · cases' abs_cases z with hz hz
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0 and all expressions are non-negative
              nlinarith
            · -- Case where x < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0 and all expressions are negative
              nlinarith
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, z < 0 and all expressions are non-negative
              nlinarith
            · -- Case where x < 0, z < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, z < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, z < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, z < 0 and all expressions are negative
              nlinarith
    · cases' abs_cases z with hz hz
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0 and all expressions are non-negative
              nlinarith
            · -- Case where x < 0, y < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0 and all expressions are negative
              nlinarith
      · cases' abs_cases (x + y - z) with h1 h1
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, z < 0 and all expressions are non-negative
              nlinarith
            · -- Case where x < 0, y < 0, z < 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0, z < 0, both x - y + z < 0 and -x + y + z < 0
              nlinarith
        · cases' abs_cases (x - y + z) with h2 h2
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0, z < 0, x + y - z < 0, x - y + z ≥ 0, -x + y + z < 0
              nlinarith
          · cases' abs_cases (-x + y + z) with h3 h3
            · -- Case where x < 0, y < 0, z < 0, x + y - z < 0, x - y + z < 0, -x + y + z ≥ 0
              nlinarith
            · -- Case where x < 0, y < 0, z < 0 and all expressions are negative
              nlinarith