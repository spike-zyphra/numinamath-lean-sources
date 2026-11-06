import Mathlib

/- Solve the equation: $2x^{2}-4x=6-3x$.-/
theorem algebra_9120 (x : ℝ) : 2 * x ^ 2 - 4 * x = 6 - 3 * x ↔ x = -3 / 2 ∨ x = 2 := by
constructor
intro h
-- main direction. solve equation
have heq: 2*x^2 - x - 6 = 0 := by
    -- 2x^2-4x=6-3x, so 2x^2-4x-6+3x=0, therefore 2x^2-x-6=0.
    have ht1: 2*x^2 - 4*x - (6-3*x) = 0 := by
        rw [h]; simp
    rw [← ht1]; ring
-- factorize 2x^2-x-6, and we get two solutions of the equation.
have h1: 2*x^2 - x - 6 = 2*(x+3/2)*(x-2) := by ring
rw [h1, mul_assoc] at heq
have h2: (x+3/2) * (x-2) = 0 := by
    have: (2:ℝ) ≠ 0 := by norm_num
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero this heq
have h3: x+3/2 = 0 ∨ x-2 = 0 := mul_eq_zero.mp h2
rcases h3 with h31 | h32
left
linarith [h31]
right
linarith [h32]
-- mpr direction. verify.
intro h
rcases h with h1 | h2
rw [h1]; norm_num
rw [h2]; norm_num