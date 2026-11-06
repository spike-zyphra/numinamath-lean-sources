import Mathlib

theorem algebra_324312 (m : ℤ) :
    (∃ x : ℤ, 2 * x ^ 2 + (1 - 2 * m) * x + m ^ 2 - 2 * m = 0) ↔
    m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
  constructor
  · -- Assume there's an integer solution x for the equation
    rintro ⟨x, hx⟩
    have h_eq : 2 * x ^ 2 + (1 - 2 * m) * x + m ^ 2 - 2 * m = 0 := hx
    have h1 : m ≥ 0 := by
      nlinarith [sq_nonneg (x - m), sq_nonneg (2 * x + (1 - 2 * m)), sq_nonneg (x - 1), sq_nonneg (m - 3)]
    have h2 : m ≤ 3 := by
      nlinarith [sq_nonneg (x - m), sq_nonneg (2 * x + (1 - 2 * m)), sq_nonneg (x - 1), sq_nonneg (m - 3)]
    interval_cases m <;> omega
  · -- Backward direction: if m in {0,1,2,3}, then there's an integer solution
    rintro (rfl | rfl | rfl | rfl)
    · -- m = 0
      use 0
      all_goals norm_num
    · -- m = 1
      use 1
      all_goals norm_num
    · -- m = 2
      use 0
      all_goals norm_num
    · -- m = 3
      use 1
      all_goals norm_num