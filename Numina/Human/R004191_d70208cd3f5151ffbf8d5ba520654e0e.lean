import Mathlib

/- The real numbers $a, b$ and $c$ satisfy the inequalities $|a| \geq|b+c|,|b| \geq|c+a|$ and $|c| \geq|a+b|$. Prove that $a+b+c=0$. -/
theorem inequalities_241546 {a b c : ℝ} (h1 : |a| ≥ |b + c|) (h2 : |b| ≥ |c + a|)
(h3 : |c| ≥ |a + b|) : a + b + c = 0:= by
    -- Convert absolute value inequalities to squared inequalities
    replace h1 : a ^ 2 ≥ (b + c) ^ 2:= by exact sq_le_sq.mpr h1
    replace h2 : b ^ 2 ≥ (c + a) ^ 2:= by exact sq_le_sq.mpr h2
    replace h3 : c ^ 2 ≥ (a + b) ^ 2:= by exact sq_le_sq.mpr h3
    -- State that (a + b + c)² is non-negative
    have h4 : (a + b + c) ^ 2 ≥ 0:= by positivity
    -- Use linarith to prove (a + b + c)² = 0
    replace h4 : (a + b + c) ^ 2 = 0:= by linarith
    -- Simplify the equation
    simp at h4
    -- Complete the proof using h4
    exact h4
