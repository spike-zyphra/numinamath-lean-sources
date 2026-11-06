import Mathlib

theorem algebra_246480 {X Y : ℕ} (hX : X + 2 * Y = 30) :
    X * Y ≤ 112 ∧ (∃ X Y : ℕ, X + 2 * Y = 30 ∧ X * Y = 112) := by

  have h1 : X ≤ 30 := by 
    omega
  have h2 : Y ≤ 15 := by 
    omega

  have h3 : X * Y ≤ 112 := by
    have h4 : X = 30 - 2 * Y := by
      omega
    rw [h4]
    -- Now need to show that (30 - 2 * Y) * Y ≤ 112 for all Y ≤ 15
    interval_cases Y <;> norm_num <;> omega

  have h4 : ∃ X Y : ℕ, X + 2 * Y = 30 ∧ X * Y = 112 := by
    exact ⟨16, 7, by norm_num, by norm_num⟩

  constructor
  · exact h3
  · exact h4