import Mathlib
/- Let $a, b, c, x$ be reals with $(a+b)(b+c)(c+a) \neq 0$ that satisfy

$$
\frac{a^{2}}{a+b}=\frac{a^{2}}{a+c}+20, \quad \frac{b^{2}}{b+c}=\frac{b^{2}}{b+a}+14, \quad \text { and } \quad \frac{c^{2}}{c+a}=\frac{c^{2}}{c+b}+x
$$

Compute $x$. -/
theorem algebra_609296 (a b c x : ℝ) (h : (a + b) * (b + c) * (c + a) ≠ 0) (h1 : a ^ 2 / (a + b) = a ^ 2 / (a + c) + 20) (h2 : b ^ 2 / (b + c) = b ^ 2 / (b + a) + 14) (h3 : c ^ 2 / (c + a) = c ^ 2 / (c + b) + x) : x = -34:= by
  -- Key insight: The sum of differences of paired fractions equals 0
  have h1 : a ^ 2 / (a + b) - b ^ 2 / (b + a) + (b ^ 2 / (b + c) - c ^ 2 / (c + b)) + (c ^ 2 / (c + a) - a ^ 2 / (a + c)) = 0:= by
    -- Simplify the non-zero condition
    simp at h
    -- Break down the conjunction into individual non-zero conditions
    rcases h with ⟨⟨g1, g2⟩, g3⟩
    -- Prove a + c ≠ 0 by rewriting and using existing condition
    have g4 : a + c ≠ 0:= by rw [show a + c = c + a by ring] ; exact g3
    -- Prove c + b ≠ 0 by rewriting and using existing condition
    have g5 : c + b ≠ 0:= by rw [show c + b = b + c by ring] ; exact g2
    -- Prove b + a ≠ 0 by rewriting and using existing condition
    have g6 : b + a ≠ 0:= by rw [show b + a = a + b by ring] ; exact g1
    -- Simplify field expressions
    field_simp
    -- Normalize ring expressions
    ring_nf
  -- Complete the proof using linear arithmetic
  linarith
