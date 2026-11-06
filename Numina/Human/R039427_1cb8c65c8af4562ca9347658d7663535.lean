import Mathlib

/- Kymbrea's comic book collection currently has 30 comic books in it,
and she is adding to her collection at the rate of 2 comic books per month.
LaShawn's collection currently has 10 comic books in it, and he is adding to
his collection at the rate of 6 comic books per month. After how many months
will LaShawn's collection have twice as many comic books as Kymbrea's?
(A) 1
(B) 4
(C) 5
(D) 20
(E) 25 -/
theorem algebra_97646 (k l : ℕ) (hk : k = 30) (hl : l = 10)
(h : l + 6 * t = 2 * (k + 2 * t)) :
t = 25 := by
  -- solve for t in equation
  rw [hk, hl] at h
  linarith