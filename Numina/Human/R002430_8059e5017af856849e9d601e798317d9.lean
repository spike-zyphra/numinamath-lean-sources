import Mathlib

/- A semipro baseball league has teams with 21 players each. League rules state that a player must be paid at least 15,000 dollars, and that the total of all players' salaries for each team cannot exceed 700,000 dollars. What is the maximum possiblle salary, in dollars, for a single player?
(A) 270,000(B) 385,000(C) 400,000(D) 430,000(E) 700,000 -/
theorem algebra_93251 (x : ℝ) (hx : x > 0) (h : 20 * 15000 + x = 700000) :
x = 400000 := by 
    --solve the expression for x using linear arithmetic
    linarith