import Mathlib

theorem algebra_227266 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hinc : ∀ n, a (n + 1) > a n) (h : ∀ n, a (n + 2) = a (n + 1) + 2 * a n)
    (h5 : a 5 = 52) : a 7 = 212 := by 
  have h7 : a 7 = a 6 + 2 * a 5 := h 5
  have h6 : a 6 = a 5 + 2 * a 4 := h 4
  have h5' : a 5 = a 4 + 2 * a 3 := h 3
  have h4 : a 4 = a 3 + 2 * a 2 := h 2
  have h3 : a 3 = a 2 + 2 * a 1 := h 1
  have h2 : a 2 = a 1 + 2 * a 0 := h 0
  have pos0 : 0 < a 0 := ha 0
  have pos1 : 0 < a 1 := ha 1
  have pos2 : 0 < a 2 := ha 2
  have pos3 : 0 < a 3 := ha 3
  have pos4 : 0 < a 4 := ha 4
  have pos5 : 0 < a 5 := ha 5
  have pos6 : 0 < a 6 := ha 6
  have pos7 : 0 < a 7 := ha 7
  have inc0 : a 1 > a 0 := hinc 0
  have inc1 : a 2 > a 1 := hinc 1
  have inc2 : a 3 > a 2 := hinc 2
  have inc3 : a 4 > a 3 := hinc 3
  have inc4 : a 5 > a 4 := hinc 4
  have inc5 : a 6 > a 5 := hinc 5
  have inc6 : a 7 > a 6 := hinc 6
  omega