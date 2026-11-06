import Mathlib

theorem number_theory_229185 (b : ℕ) (hb : b ≤ 10) :
    (5 * b + 2 * (10 - b)) ≠ 45 ∧
    (5 * b + 2 * (10 - b)) ≠ 39 ∧
    (5 * b + 2 * (10 - b)) ≠ 37 ∧
    (5 * b + 2 * (10 - b)) ≠ 31 := by 
  have h1 : (5 * b + 2 * (10 - b)) ≠ 45 := by 
    omega 
  have h2 : (5 * b + 2 * (10 - b)) ≠ 39 := by 
    omega 
  have h3 : (5 * b + 2 * (10 - b)) ≠ 37 := by 
    omega 
  have h4 : (5 * b + 2 * (10 - b)) ≠ 31 := by 
    omega 
  exact ⟨h1, h2, h3, h4⟩