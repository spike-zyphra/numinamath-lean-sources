import Mathlib

theorem algebra_12558 {n d q : ℕ} (h : n = d ∧ d = q) (h' : 5*n+10*d+25*q=1320) :
    n = 33 := by
  rcases h with ⟨hx1, hx2⟩
  omega