import Mathlib

theorem number_theory_159969 (x : ℝ) (hx : x ≠ 0) (hA : (1 / x ≥ 1) ∨ (Nat.floor x ≠ 6) ∨ (x ^ 3 < 221))
    (hB : Even x ∨ Prime x ∨ 5 ∣ x) (hC : ¬∃ a b, x = a / b ∨ x < 6 ∨ ∃ n, x = n ^ 2)
    (hD : x > 20 ∨ (10 ≤ x ∧ x < 100) ∨ ¬∃ k, x = k ^ 2) :
    x = 25 := by 
  have h1 : ∃ a b, x = a / b ∨ x < 6 ∨ ∃ n, x = n ^ 2 := by
    use x, 1
    left
    field_simp
  contradiction