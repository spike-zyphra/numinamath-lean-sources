import Mathlib

theorem number_theory_177146 (x y : ℕ) (hx : x < 10) (hy : y < 10)
    (h : (10^200 * 89252525 + x * 1000 + y) * (44400000 + 100 * x + y) =
      10^53 + 10^54) :
    x = 4 ∧ y = 6 := by 
  have h_eq : (10^200 * 89252525 + x * 1000 + y) * (44400000 + 100 * x + y) = 10^53 + 10^54 := h
  have h1 : x < 10 := hx
  have h2 : y < 10 := hy
  interval_cases x <;> interval_cases y <;> omega