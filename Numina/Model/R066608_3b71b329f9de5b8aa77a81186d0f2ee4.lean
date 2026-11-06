import Mathlib

theorem algebra_315513 {x y : ℕ} (hx : x ≤ 10) (hy : y ≤ 10)
    (h : x + y = 28) :
    IsLeast {w | ∃ x y : ℕ, x ≤ 10 ∧ y ≤ 10 ∧ x + y = 28 ∧ w = 200 * x + 800 * (10 - x) +
      300 * y + 700 * (10 - y) + 400 * (28 - x - y) + 500 * (10 - (28 - x - y))} 9800 ∧
    IsGreatest {w | ∃ x y : ℕ, x ≤ 10 ∧ y ≤ 10 ∧ x + y = 28 ∧ w = 200 * x + 800 * (10 - x) +
      300 * y + 700 * (10 - y) + 400 * (28 - x - y) + 500 * (10 - (28 - x - y))} 14200 := by
  constructor
  · -- First part: prove that 9800 is the least element in the set
    constructor
    · -- We need to prove 9800 is in the set
      use 10, 18
      all_goals omega
    · -- We need to prove 9800 is the minimum
      intro w hw
      rcases hw with ⟨x, y, hx, hy, hxy, hw⟩
      -- Now we need to show that w >= 9800 for all valid x, y
      have h1 : x ≤ 10 := hx
      have h2 : y ≤ 10 := hy
      have h3 : x + y = 28 := hxy
      -- This is a contradiction because x + y <= 10 + 10 = 20 < 28
      omega
  · -- Second part: prove that 14200 is the greatest element in the set
    constructor
    · -- We need to prove 14200 is in the set
      use 0, 28
      all_goals omega
    · -- We need to prove 14200 is the maximum
      intro w hw
      rcases hw with ⟨x, y, hx, hy, hxy, hw⟩
      -- Now we need to show that w <= 14200 for all valid x, y
      have h1 : x ≤ 10 := hx
      have h2 : y ≤ 10 := hy
      have h3 : x + y = 28 := hxy
      -- This is a contradiction because x + y <= 10 + 10 = 20 < 28
      omega