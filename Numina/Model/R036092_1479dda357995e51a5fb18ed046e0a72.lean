import Mathlib

open Nat 

def G (n : ℕ) := fib (3 * n)

theorem algebra_21722 {a b : ℤ} (ha : ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)) :
    a = 4 ∧ b = 1 := by 
  have eq1 := ha 2 (by norm_num)
  have eq2 := ha 3 (by norm_num)
  simp [G, fib] at eq1 eq2 
  have h1 : (a : ℤ) = 4 := by
    norm_num at eq1
    linarith
  have h2 : (b : ℤ) = 1 := by 
    norm_num [h1] at eq2
    linarith
  exact ⟨h1, h2⟩