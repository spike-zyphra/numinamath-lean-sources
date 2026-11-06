import Mathlib

open Finset

/-- A list of $11$ positive integers has a mean of $10$, a median of $9$, and a unique mode of $8$.
What is the largest possible value of an integer in the list?

$\textbf{(A)}\ 24\qquad\textbf{(B)}\ 30\qquad\textbf{(C)}\ 31\qquad\textbf{(D)}\ 33\qquad\textbf{(E)}\
35$ -/
theorem number_theory_94247
    (A : Finset ℕ) (hA : A = Icc 5 8) (B : Finset ℕ) (hB : B = Icc 1 4) :
    ((((A ×ˢ B).image (fun (a, b) ↦ 10 * a + b)).filter IsSquare).card : ℚ) / (A ×ˢ B).card = 1 / 8 := by

  -- Let $s$ be the set of square numbers that can be formed using the numbers in the spinners.
  set s := ((A ×ˢ B).image (fun (a, b) ↦ 10 * a + b)).filter IsSquare

  -- First, we calculate that there are a total of $4\cdot4=16$ possibilities.
  have : (A ×ˢ B).card = 16 := by rw [card_product, hA, hB, Nat.card_Icc, Nat.card_Icc]
  rw [this]

  -- We need to show that we can form two square numbers using the numbers in the spinners.
  suffices s.card = 2 by rw [this]; norm_num

  -- Actually, we can show that $s = \{16, 64\}$ by trying all the possibilities.
  have : s = {64, 81} := by simp [s, hA, hB, this]; decide +kernel
  simp [this]