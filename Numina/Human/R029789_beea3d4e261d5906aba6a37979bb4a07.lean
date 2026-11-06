import Mathlib
/- Soit $a, b, c$ des nombres réels. Montrer que:

$$
2 a^{2}+20 b^{2}+5 c^{2}+8 a b-4 b c-4 a c \geqslant 0
$$

et trouver les cas d'égalité. -/
theorem algebra_607250 (a b c : ℝ) :
    2 * a ^ 2 + 20 * b ^ 2 + 5 * c ^ 2 + 8 * a * b - 4 * b * c - 4 * a * c ≥ 0 ∧
    (2 * a ^ 2 + 20 * b ^ 2 + 5 * c ^ 2 + 8 * a * b - 4 * b * c - 4 * a * c = 0 ↔
      (a = 0 ∧ b = 0 ∧ c = 0)):= by
        -- We first establish three non-negative squared terms that will help prove the inequality
        -- Square of (a - 2c) is ≥ 0
        have h1 : (a - 2 * c) ^ 2 ≥ 0:= by positivity
        -- Square of (2b - c) is ≥ 0
        have h2 : (2 * b - c) ^ 2 ≥ 0:= by positivity
        -- Square of (a + 4b) is ≥ 0
        have h3 : (a + 4 * b) ^ 2 ≥ 0:= by positivity
        constructor
        -- First part: proving the expression is non-negative using linear arithmetic
        . linarith
        -- Second part: proving the equality case (bidirectional implication)
        . constructor
          -- Forward direction: proving that if expression = 0, then a = b = c = 0
          . intro h
            -- If sum of squares is 0, each square must be 0
            replace h1 : (a - 2 * c) ^ 2 = 0:= by linarith
            replace h2 : (2 * b - c) ^ 2 = 0:= by linarith
            replace h3 : (a + 4 * b) ^ 2 = 0:= by linarith
            -- If square is 0, the term itself must be 0
            replace h1 : a - 2 * c = 0:= by exact pow_eq_zero h1
            replace h2 : 2 * b - c = 0:= by exact pow_eq_zero h2
            replace h3 : a + 4 * b = 0:= by exact pow_eq_zero h3
            -- Prove all variables are 0 using the system of equations
            refine ⟨?_, ?_, ?_⟩
            all_goals
            linarith
          -- Reverse direction: proving that if a = b = c = 0, then expression = 0
          . intro h
            -- Break down the hypothesis into individual components
            rcases h with ⟨h1, h2, h3⟩
            -- Substitute the values of a, b, c with 0
            subst a b c
            -- Simplify the expression to complete the proof
            simp
