import Mathlib

theorem number_theory_639166 (N : ℕ) (hN : N > 0) :
  IsGreatest {x | ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a^2 + b^2 + c^2 + d^2 = 4 * N^2 + 2 * N + 1 ∧ x = a + b + c + d} (4 * N + 1) := by 
  unfold IsGreatest
  constructor
  · -- Prove that there exists such integers $a$, $b$, $c$, and $d$ for which the expression takes the value $4N+1$
    simp
    use N
    constructor
    linarith
    use N 
    constructor
    linarith
    use N
    constructor
    linarith
    use N + 1
    constructor
    linarith
    constructor
    ring
    ring
  · unfold upperBounds
    simp
    intro x a ha b hb c hc d hd h h'
    have h1 : ((a : ℝ) + b + c + d) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * 4 := by 
      have aux : ((a : ℝ) - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2 ≥ 0 := by positivity
      linarith
    norm_cast at h1
    rw [←h', h] at h1
    have eq1 : (4 * N ^ 2 + 2 * N + 1) * 4 = (4 * N + 1) ^ 2 + 3 := by 
      ring
    rw [eq1] at h1
    have xlt : x < 4 * N + 2 := by 
      by_contra hc1
      simp at hc1
      have xsq_ge : x ^ 2 ≥ (4 * N + 2) ^ 2 := by 
        exact Nat.pow_le_pow_of_le_left hc1 2
      linarith
    exact Nat.le_of_lt_succ xlt