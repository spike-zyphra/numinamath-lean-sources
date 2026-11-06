import Mathlib

theorem algebra_234243 (x y z : ℤ) :
    2 * x ^ 2 + 2 * x ^ 2 * z ^ 2 + z ^ 2 + 7 * y ^ 2 - 42 * y + 33 = 0 ↔
    (x = 1 ∧ y = 5 ∧ z = 0) ∨ (x = -1 ∧ y = 5 ∧ z = 0) ∨
    (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = -1 ∧ y = 1 ∧ z = 0) := by
  constructor
  · -- Assume the equation holds, prove the disjunction of the solutions
    rintro h_eq
    have h_eq2 : 2 * x ^ 2 * (1 + z ^ 2) + z ^ 2 + 7 * (y - 3) ^ 2 = 30 := by 
      nlinarith
    have h1 : y ≤ 5 := by
      nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (z : ℤ), sq_nonneg (x : ℤ)]
    have h2 : y ≥ 1 := by 
      nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (z : ℤ), sq_nonneg (x : ℤ)]
    have h3 : z ≤ 5 := by
      nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (z : ℤ), sq_nonneg (x : ℤ)]
    have h4 : z ≥ -5 := by
      nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (z : ℤ), sq_nonneg (x : ℤ)]
    interval_cases y <;> interval_cases z
    <;> try { 
      have : x ≤ 5 := by nlinarith 
      have : x ≥ -5 := by nlinarith 
      interval_cases x 
      <;> omega 
    }
  · -- Assume the disjunction of the solutions, prove the equation
    rintro (h | h | h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · -- Third solution
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num
    · -- Fourth solution
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num