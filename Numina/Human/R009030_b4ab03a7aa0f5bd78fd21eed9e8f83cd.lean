import Mathlib

/- A set contains four numbers. 
The six pairwise sums of distinct elements of the set, in no particular order, are 189, 320, 287, 234, x, and y. 
Find the greatest possible value of x + y. -/
theorem algebra_14282 (a b c d x y : ℝ)
(h₀ : a > b ∧ b > c ∧ c > d)
(h₁ : a + b = x ∧ a + c = y ∧ a + d = 320 ∧ b + c = 287 ∧ b + d = 189 ∧ c + d = 234) :
x + y = 791 := by
  obtain ⟨h1,h2,h3,h4, h5, h6⟩:=h₁
  --rewrite the two largest sums as x and y
  rw[← h1,← h2]
  ring_nf
  --rewrite x+y as an equality involving any other number, which is already given.
  have h: a * 2 + b + c = 3 * ((a + d) + (b + c)) - ((a + d) + (b + c) + (b + d) + (c + d)) := by ring_nf
  rw[h]
  --substitute and solve the linear arithmetic
  rw[h3,h4,h5,h6]
  ring_nf