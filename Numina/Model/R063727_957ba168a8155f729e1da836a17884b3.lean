import Mathlib

theorem algebra_326618 {p1 p2 q1 q2 : ℝ} (h : p1 * p2 = 2 * (q1 + q2)) :
    ∃ x : ℝ, x ^ 2 + p1 * x + q1 = 0 ∨ x ^ 2 + p2 * x + q2 = 0 := by 
  by_cases h₁ : p1 ^ 2 - 4 * q1 ≥ 0
  · -- If $p_1^2 - 4q_1 \geq 0$, then $x^2 + p_1x + q_1 = 0$ has real roots
    use (-p1 + Real.sqrt (p1 ^ 2 - 4 * q1)) / 2
    left
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    linarith
  · -- Assume $p_1^2 - 4q_1 < 0$, we have to prove $x^2 + p_2 x + q_2 = 0$ has real roots
    have h₂ : p1 ^ 2 - 4 * q1 < 0 := by linarith
    by_cases h₂₂ : p2 ^ 2 - 4 * q2 ≥ 0
    · -- If $p_2^2 - 4q_2 \geq 0$, then $x^2 + p_2 x + q_2 = 0$ has real roots
      use (-p2 + Real.sqrt (p2 ^ 2 - 4 * q2)) / 2
      right
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      linarith
    · -- Assume $p_2^2 - 4q_2 < 0$, we have to derive a contradiction
      have h₂₂₂ : p2 ^ 2 - 4 * q2 < 0 := by linarith
      -- First, from $p_1^2 - 4q_1 < 0$, we know $p_1^2 < 4q_1$.
      have h₁₁ : p1 ^ 2 < 4 * q1 := by linarith
      -- From $p_2^2 - 4q_2 < 0$, we know $p_2^2 < 4q_2$.
      have h₂₂₂₂ : p2 ^ 2 < 4 * q2 := by linarith
      -- Therefore $p_1^2 + p_2^2 < 4(q_1 + q_2)$.
      have h₃ : p1 ^ 2 + p2 ^ 2 < 4 * (q1 + q2) := by linarith
      -- But $p_1p_2 = 2(q_1 + q_2)$ from the hypothesis, so $4(q_1 + q_2) = 2p_1p_2$
      -- Therefore $p_1^2 + p_2^2 < 2p_1p_2$.
      -- So $(p_1 - p_2)^2 < 0$ which is impossible.
      have h₄ : p1 ^ 2 + p2 ^ 2 - 2 * (p1 * p2) < 0 := by nlinarith [h]
      -- But $(p_1 - p_2)^2 \geq 0$ which would lead to a contradiction
      nlinarith [sq_nonneg (p1 - p2)]