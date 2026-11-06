import Mathlib

theorem algebra_3089 : IsGreatest {x : ℤ | ∃ y : ℤ, x^2-6*x*y+13*y^2=200} 25 := by
  constructor
  · -- Show 25 is in the set
    use 5
    norm_num
  · -- Show if x is in the set, then x ≤ 25
    intro x hx
    rcases hx with ⟨y, hy⟩
    have h1 : x^2 - 6 * x * y + 13 * y^2 = 200 := by linarith
    have h2 : (x - 3 * y) ^ 2 + 4 * y ^ 2 = 200 := by
      nlinarith [h1]
    have h3 : y ≥ -7 := by 
      nlinarith [sq_nonneg (x - 3 * y), sq_nonneg (y)]
    have h4 : y ≤ 7 := by
      nlinarith [sq_nonneg (x - 3 * y), sq_nonneg (y)]
    interval_cases y <;> try { nlinarith [sq_nonneg (x - 25)] }
    all_goals
      nlinarith