import Mathlib

/-
A rectangular chocolate bar is made of equal squares. Irena breaks off two complete strips of squares and eats the 12 squares she obtains. Later, Jack breaks off one complete strip of squares from the same bar and eats the 9 squares he obtains. How many squares of chocolate are left in the bar?
A 72
В 63
C 54
D 45
E 36
-/

theorem number_theory_230602 (n m : ℕ) (hnm : n > 0 ∧ m > 0)
    (h: 2*n = 12 ∧ (1*n = 9 ∨ 1*(m-2) = 9)):
    n * m - 12 - 9 = 45 := by
    obtain ⟨h1, h2⟩ := h
    have neq6 : n = 6 := by omega
    obtain tmp1 | tmp2 := h2
    omega
    have meq11 : m = 11 := by omega
    simp [neq6, meq11]
