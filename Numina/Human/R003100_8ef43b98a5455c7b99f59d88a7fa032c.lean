import Mathlib

/- ## Task 31/72

Prove: If the real numbers $a, b, c, d$ satisfy the four inequalities


$$

\begin{aligned}
a+b+c+d & >0 \\
a b+a c+a d+b c+b d+c d & >0 \\
a b c+a b d+a c d+b c d & >0 \\
a b c d & >0
\end{aligned}

$$


then $a, b, c, d$ are positive numbers. -/
theorem inequalities_153029 (a b c d : ℝ)
    (h₀ : a + b + c + d > 0)
    (h₁ : a * b + a * c + a * d + b * c + b * d + c * d > 0)
    (h₂ : a * b * c + a * b * d + a * c * d + b * c * d > 0)
    (h₃ : a * b * c * d > 0) :
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 := by
  -- It is enough to show that the conditions imply that a > 0.
  suffices ∀ a b c d : ℝ, a + b + c + d > 0
      → a * b + a * c + a * d + b * c + b * d + c * d > 0
      → a * b * c + a * b * d + a * c * d + b * c * d > 0
      → a * b * c * d > 0
      → a > 0 by
    constructorm* _ ∧ _
    · apply this a b c d h₀ h₁ h₂ h₃
    · apply this b a c d (by linarith) (by linarith) (by linarith) (by linarith)
    · apply this c a b d (by linarith) (by linarith) (by linarith) (by linarith)
    · apply this d a b c (by linarith) (by linarith) (by linarith) (by linarith)
  clear * -
  intro a b c d h1 h2 h3 h4
  -- Suppose that a ≤ 0 and derive a contradiction.
  by_contra ha
  simp at ha
  -- a ≤ 0 implies that a < 0 because a * b * c * d ≠ 0.
  replace ha : a < 0 := by
    rw [lt_iff_le_and_ne]
    refine ⟨ha, ?_⟩
    contrapose! h4
    simp [h4]
  -- Define p, q, r, s.
  set p := a + b + c + d
  set q := a * b + a * c + a * d + b * c + b * d + c * d
  set r := a * b * c + a * b * d + a * c * d + b * c * d
  set s := a * b * c * d
  -- We have a ^ 4 + p * (-a) ^ 3 + q * a ^ 2 + r * (-a) + s = 0.
  have eq : a ^ 4 + p * (-a) ^ 3 + q * a ^ 2 + r * (-a) + s = 0 := by ring
  -- Show that a < 0 implies that 0 < a ^ 4 + p * (-a) ^ 3 + q * a ^ 2 + r * (-a) + s.
  contrapose! eq
  apply ne_of_gt
  suffices 0 < a ^ 4 ∧ 0 < p * (-a) ^ 3 ∧ 0 < q * a ^ 2 ∧ 0 < r * (-a) by linarith
  constructorm* _ ∧ _
  -- 0 < a ^ 4 because a ≠ 0.
  · have := ne_of_lt ha
    positivity
  -- 0 < p * (-a)^3 because p > 0 and -a > 0.
  · have : 0 < -a := by linarith
    positivity
  -- 0 < q * a ^ 2 because q > 0 and a ≠ 0.
  · have := ne_of_lt ha
    positivity
  -- 0 < r * (-a) because r > 0 and -a > 0.
  · have : 0 < -a := by linarith
    positivity