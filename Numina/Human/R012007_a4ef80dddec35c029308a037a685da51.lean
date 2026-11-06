import Mathlib

/- 334. Solve the system of equations:

$$
\left\{\begin{array}{l}
x^{2}+y z=y+z \\
y^{2}+x z=x+z \\
z^{2}+x y=x+y
\end{array}\right.
$$ -/
theorem algebra_188099 (x y z : ℝ) :
    x^2 + y * z = y + z ∧ y^2 + x * z = x + z ∧ z^2 + x * y = x + y ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = -1 ∧ y = 1 ∧ z = 1) ∨ (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = -1) := by

    constructor

    --From left to right. We subtract the second equation from the first one and subtract the third equation from the second one.
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    have eq1 : (x+y+1-z) * (x-y) = 0 := by nlinarith
    have cla1: (x+y+1-z) = 0 ∨ (x-y) = 0 := by exact mul_eq_zero.mp eq1
    have eq2 : (y+z+1-x) * (y-z) = 0 := by nlinarith
    have cla2: (y+z+1-x) = 0 ∨ (y-z) = 0 := by exact mul_eq_zero.mp eq2

    --We consider all possible cases for these two pairs of possibilities.
    rcases cla1 with c1 | c1
    
    rcases cla2 with c2 | c2

    have yeq : y = -1 := by linarith
    have xeqz: x = z := by linarith
    have : x = 1 := by nlinarith
    have : z = 1 := by linarith
    right; right; right; left; tauto

    have : x = -1 := by linarith
    have : y = z := by linarith
    have : y = 1 := by nlinarith
    have : z = 1 := by linarith
    right;right;left; tauto

    rcases cla2 with c2 | c2

    have : z = -1 := by linarith
    have : x = y := by linarith
    have : x = 1 := by nlinarith
    have : y = 1 := by linarith
    right;right;right;right;tauto

    have : x = y := by linarith
    have : y = z := by linarith

    have mul0: x * (x-1) = 0 := by nlinarith
    have : x = 0 ∨ x - 1 = 0 := by exact mul_eq_zero.mp mul0
    rcases this with t | t
    have :x = 0 := by linarith
    have :y = 0 := by linarith
    have :z = 0 := by linarith
    left; tauto
    have :x = 1 := by linarith
    have :y = 1 := by linarith
    have : z = 1 := by linarith
    right; left; tauto

    --From right to left. Simple calculation to verify that all 5 solutions are valid.
    intro h
    rcases h with h | h | h | h | h
    repeat simp [h]
    