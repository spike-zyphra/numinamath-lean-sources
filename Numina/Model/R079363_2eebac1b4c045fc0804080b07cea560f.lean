import Mathlib

theorem number_theory_184741 (a s : Finset ℤ) (ha : ∀ n ∈ a, n > 0)
    (hs : ∃ x ∈ a, x < 0) (h : ∑ n ∈ a, n = 5 * ∏ n ∈ a, n) :
    x = 6 ∨ x = -20 := by 
  rcases hs with ⟨x, hx1, hx2⟩ 
  have h1 : x > 0 := ha x hx1
  linarith