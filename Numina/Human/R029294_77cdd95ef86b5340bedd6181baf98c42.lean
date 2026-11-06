import Mathlib

/- Which of the following numbers is a perfect square?
(A) 14!*15!/2 (B) 15!*16!/2 (C) 16!*17!/2 (D) 17!*18!/2 (E) 18!*19!/2 -/
theorem number_theory_94822 : IsSquare ((Nat.factorial 17) * (Nat.factorial 18) / 2) := by {
  -- Specify which number it is the square of. To obtain this, factor out n!^2 out of each of the numbers. The other
  -- factor is then (n+1)/2, and for the numbers above this is a square precisely for n = 17.
  use (Nat.factorial 17)*3
  -- Factor 18! = 17!*18
  rw [Nat.factorial.eq_2 17]
  -- Simplify the equation, which lets us factor out 17!^2 on each side
  ring_nf
  -- Verify the equality. Since division here is integer division, we use that 18 is even (which is trivial).
  rw [Nat.mul_div_assoc]
  norm_num
  trivial
}