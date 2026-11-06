import Mathlib

theorem number_theory_277831 (a : ℕ → ℕ) (ha : ∀ n, a n = if n % 5 = 0 then 5 else if n % 5 = 1 then 6 else if n % 5 = 2 then 7 else if n % 5 = 3 then 8 else 9) :
    a 220 = 5 := by
  have h : a 220 = if 220 % 5 = 0 then 5 else if 220 % 5 = 1 then 6 else if 220 % 5 = 2 then 7 else if 220 % 5 = 3 then 8 else 9 := ha 220
  norm_num [h]
  <;> omega -- This will simplify the arithmetic in the hypothesis `h` to show that it indeed gives `a 220 = 5`.