import Mathlib

/-
10. Let $ab$ be a two-digit number in decimal notation, and let $ba$ be the two-digit number formed by swapping the unit and tens digits, the product of these two two-digit numbers is 4930, find the values of $a$ and $b$.
-/

theorem algebra_318088 (a b x y: ℕ) (ua: a ≤ 9) (ub: b ≤ 9) (hx:x=10*a+b) (hy:y=10*b+a): 
  x*y = 4930 ↔ a = 5 ∧ b = 8 ∨ a = 8 ∧ b = 5 := by

  constructor

  --From left to right.
  intro h

  --By our assumption, we have 10. $(10 a+b)(10 b+a)=4930$.
  simp [hx,hy] at h

  --Then 5 ≤ a, since otherwise the left-hand side is too small.
  have age5 : 5 ≤ a := by 
    nlinarith
  have bge5 : 5 ≤ b := by
    nlinarith

  --We check every case from a = 5 to a = 9.
  by_cases ae : a = 5
  simp [ae] at h
  have be : b = 8 := by nlinarith
  tauto
  by_cases ae : a = 6
  exfalso
  simp [ae] at h
  ring_nf at h
  have : 6 < b := by nlinarith
  have : b < 7 := by nlinarith
  linarith

  by_cases ae : a = 7
  exfalso
  simp [ae] at h
  ring_nf at h
  omega
  by_cases ae : a = 8
  simp [ae] at h
  have be : b = 5 := by nlinarith
  tauto
  have ae : a = 9 := by omega
  exfalso
  simp [ae] at h
  nlinarith

  --From right to left. Simple verification.
  intro h
  rcases h with ⟨ae,be⟩ | ⟨ae,be⟩
  all_goals 
  simp [hx,hy,ae,be]

