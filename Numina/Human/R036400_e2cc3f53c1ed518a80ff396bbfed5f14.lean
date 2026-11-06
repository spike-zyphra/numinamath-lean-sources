import Mathlib

open Real Set
open scoped BigOperators

/- Let $a, b$ be positive real numbers, and let $M=\begin{cases}ab, & ab\leqslant \frac{4}{{{a}^{2}}+4{{b}^{2}}} \\ \frac{4}{{{a}^{2}}+4{{b}^{2}}}, & ab>\frac{4}{{{a}^{2}}+4{{b}^{2}}} \end{cases}$, then the maximum value of $M$ is ___          ___. -/
theorem algebra_630875 :
  IsGreatest {M | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ M = if a * b ≤ 4 / (a ^ 2 + 4 * b ^ 2) then a * b else 4 / (a ^ 2 + 4 * b ^ 2)} 1 := by
  constructor
  · -- First, we show that 1 belongs to the set.
    -- Take a = √2 and b = √(1 / 2).
    use Real.sqrt 2, Real.sqrt (1 / 2), by positivity, by positivity, ?_
    -- Show that M = 1 is achieved.
    norm_num
  · -- Now we prove that 1 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h_eq⟩
    rw [h_eq]
    clear h_eq
    split_ifs with hab
    · -- Suppose ab ≤ 4 / (a² + b²), we show that M = a * b ≤ 1.
      -- Clear out denominators at hypothesis hab.
      rw [le_div_iff₀ (by positivity)] at hab
      have h₀ : 4 * (a * b) ^ 2 ≤ 4 := by
        calc
          _ = a * b * (4 * a * b) := by ring
          _ ≤ a * b * (a ^ 2 + 4 * b ^ 2) := by
            -- It suffices to use the fact that 4ab ≤ a² + 4b², which is equivalent to (a - 2b)² ≥ 0.
            nlinarith only [sq_nonneg (a - 2 * b), mul_pos ha hb]
          _ ≤ 4 := hab
      -- Now we get ab ≤ 1.
      nlinarith
    · -- Suppose ab > 4 / (a² + b²), we show that M = 4 / (a² + b²) ≤ 1.
      push_neg at hab
      -- Clear out denominators at both hypothesis and goal.
      rw [div_lt_iff₀ (by positivity)] at hab
      rw [div_le_iff₀ (by positivity)]
      have h₀ : 4 ^ 2 ≤ (a ^ 2 + 4 * b ^ 2) ^ 2 := by
        calc
          _ ≤ (4 * a * b) * (a ^ 2 + 4 * b ^ 2) := by
            linarith only [hab]
          _ ≤ (a ^ 2 + 4 * b ^ 2) * (a ^ 2 + 4 * b ^ 2) := by
            rw [mul_le_mul_right (by positivity)]
            -- It suffices to use the fact that 4ab ≤ a² + 4b², which is equivalent to (a - 2b)² ≥ 0.
            linarith only [sq_nonneg (a - 2 * b)]
          _ = (a ^ 2 + 4 * b ^ 2) ^ 2 := by
            ring
      -- Simplify to get 4 ≤ a² + 4b².
      rw [sq_le_sq₀ (by norm_num) (by positivity)] at h₀
      simp [h₀]
