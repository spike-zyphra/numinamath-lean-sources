import Mathlib

theorem algebra_313782 (a : ℤ) (ha : 0 < a) :
    ∃ x : ℝ, a * x ^ 2 + 2 * (2 * a - 1) * x + 4 * (a - 3) = 0 ↔
    a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10 := by
  by_cases h1 : a = 1
  · -- If a = 1, let's find an x that satisfies the equation.
    use -4
    simp [h1]
    <;> norm_num
  by_cases h3 : a = 3
  · -- If a = 3, let's find an x that satisfies the equation.
    use 0
    simp [h3]
    <;> norm_num
  by_cases h6 : a = 6
  · -- If a = 6, let's find an x that satisfies the equation.
    use -3
    simp [h6]
    <;> norm_num
  by_cases h10 : a = 10
  · -- If a = 10, let's find an x that satisfies the equation.
    use -1
    simp [h10]
    <;> norm_num
  · -- Case where a is none of the above.
    have h1' : a ≠ 1 := by
      omega
    have h3' : a ≠ 3 := by
      omega
    have h6' : a ≠ 6 := by
      omega
    have h10' : a ≠ 10 := by
      omega
    use (1 : ℝ)
    constructor
    · -- Forward direction: if the equation holds, then a is in the set.
      intro h
      have h_eq : (9 * (a : ℝ) - 14) = (0 : ℝ) := by
        nlinarith
      have h9 : (9 * (a : ℤ) : ℝ) = (14 : ℝ) := by
        nlinarith
      have h9' : 9 * (a : ℤ) = 14 := by
        exact_mod_cast (show (9 * (a : ℤ) : ℝ) = (14 : ℝ) by linarith)
      exfalso
      omega
    · -- Backward direction: if a is in the set, then the equation holds.
      intro h
      cases h with
      | inl h1 => 
        exfalso
        tauto
      | inr h3 => cases h3 with
        | inl h3 => 
          exfalso
          tauto
        | inr h6 => cases h6 with
          | inl h6 => 
            exfalso
            tauto
          | inr h10 => 
            exfalso
            tauto