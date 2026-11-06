import Mathlib

open Finset

theorem number_theory_96886 (s : Finset (ℕ × ℕ)) (hs : s = range 13 ×ˢ range 13)
    (t : Finset (ℕ × ℕ)) (ht : t = {p ∈ s | Odd (p.1 * p.2)}) :
    (t.card : ℚ) / s.card = 36 / 169 := by
  have h1 : s.card = 169 := by 
    rw [hs]
    native_decide
  have h2 : t.card = 36 := by 
    rw [ht]
    rw [hs]
    native_decide
  rw [h2]
  rw [h1]
  all_goals norm_num