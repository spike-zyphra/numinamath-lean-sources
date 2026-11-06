import Mathlib

open Nat

def I : ℕ → ℕ
| n => if Nat.Prime n then 1 else 0

theorem number_theory_328438 :
    ¬(∀ x y, Nat.Prime x → Nat.Prime y → I (x + y) = 0) ∧
    ¬(∀ x y, ¬Nat.Prime x → ¬Nat.Prime y → I (x + y) = 0) ∧
    ¬(∀ x y, Nat.Prime x → ¬Nat.Prime y → I (x + y) = 0) := by
  constructor
  · -- Show that proposition 1 is false
    intro h
    have h1 := h 2 3 (by norm_num) (by norm_num)
    norm_num [I] at h1
  constructor
  · -- Show that proposition 2 is false
    intro h
    have h2 := h 4 9 (by norm_num) (by norm_num)
    norm_num [I] at h2
  · -- Show that proposition 3 is false
    intro h
    have h3 := h 3 4 (by norm_num) (by norm_num)
    norm_num [I] at h3