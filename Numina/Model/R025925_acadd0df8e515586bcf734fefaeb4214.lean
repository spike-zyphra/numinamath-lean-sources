import Mathlib

theorem inequalities_33359 (a : Fin 2022 → ℤ) (ha : ∀ i j, a i = a j → i = j)
    (ha1 : a 0 = a 2020) (ha2 : a 1 = a 2021) :
    ∃ n, 1 ≤ n ∧ n ≤ 2020 ∧ a n ^ 2 + a (n + 1) ^ 2 ≥ a (n + 2) ^ 2 + n ^ 2 + 3 := by
  have h1 : (0 : Fin 2022) = (2020 : Fin 2022) := by 
    have h1 : a 0 = a 2020 := ha1
    have h2 := ha (0) (2020) h1
    exact h2
  have h2 : (0 : Fin 2022) ≠ (2020 : Fin 2022) := by 
    native_decide
  contradiction