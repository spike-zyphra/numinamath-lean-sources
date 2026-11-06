import Mathlib

theorem algebra_305443 (x y : ℕ) (h₀ : 5 ∣ x + 2 * y) (h₁ : 3 ∣ x + y)
    (h₂ : 99 ≤ 2 * x + y) :
    7 * x + 5 * y ≥ 366 := by
  have h3 : x % 15 = 0 ∨ x % 15 = 1 ∨ x % 15 = 2 ∨ x % 15 = 3 ∨ x % 15 = 4 ∨ x % 15 = 5 ∨ x % 15 = 6 ∨ x % 15 = 7 ∨ x % 15 = 8 ∨ x % 15 = 9 ∨ x % 15 = 10 ∨ x % 15 = 11 ∨ x % 15 = 12 ∨ x % 15 = 13 ∨ x % 15 = 14 := by
    omega
  have h4 : y % 15 = 0 ∨ y % 15 = 1 ∨ y % 15 = 2 ∨ y % 15 = 3 ∨ y % 15 = 4 ∨ y % 15 = 5 ∨ y % 15 = 6 ∨ y % 15 = 7 ∨ y % 15 = 8 ∨ y % 15 = 9 ∨ y % 15 = 10 ∨ y % 15 = 11 ∨ y % 15 = 12 ∨ y % 15 = 13 ∨ y % 15 = 14 := by
    omega
  rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
    try { 
      omega 
    } <;> try { 
      have : (x + 2 * y) % 5 = 0 := by 
        omega 
      have : (x + y) % 3 = 0 := by 
        omega 
      omega 
    }