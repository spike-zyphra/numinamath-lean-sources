import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_296199 {f : ℝ → ℝ}
  (hf : f = λ x => (log x * log (x ^ 2) + log (x ^ 3) + 3) / (log x ^ 2 + log (x ^ 2) + 2)) :
  IsGreatest (range f) 2.5 ∧
  ∃ x, f x = 2.5 ∧ x > 0 := by
  constructor
  · -- Let us prove that $2.5$ is the greatest element in the range of $f$, i.e., $2.5$ is attained and $\forall y \in \text{range}\ f, y \leq 2.5$
    constructor
    · -- Show that $2.5$ can be attained, i.e., exists some $x$ such that $f(x) = 2.5$
      use (Real.exp (-2 : ℝ))
      -- Now need to show $f(e^{-2}) = 2.5$
      rw [hf]
      have h0 : log (Real.exp (-2 : ℝ)) = -2 := by
        simp [Real.log_exp]
      have h1 : log ((Real.exp (-2 : ℝ) ) ^ 2) = -4 := by
        calc
          log ((Real.exp (-2 : ℝ) ) ^ 2) = 2 * log (Real.exp (-2 : ℝ)) := by
            simp [log_pow]
          _ = 2 * (-2) := by
            rw [h0]
          _ = -4 := by norm_num
      have h2 : log ((Real.exp (-2 : ℝ) ) ^ 3) = -6 := by
        calc
          log ((Real.exp (-2 : ℝ) ) ^ 3) = 3 * log (Real.exp (-2 : ℝ)) := by
            simp [log_pow]
          _ = 3 * (-2) := by
            rw [h0]
          _ = -6 := by norm_num
      simp only [h0, h1, h2]
      -- Compute numerator and denominator
      norm_num
      <;> simp [h0, h1, h2]
      <;> norm_num
      <;> tauto
      all_goals norm_num
      all_goals linarith
    · -- Now need to show that $\forall y \in range\ f, y \leq 2.5$
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp [show log (x ^ 2) = 2 * log x by simp [log_pow],
        show log (x ^ 3) = 3 * log x by simp [log_pow]] at hx
      by_contra h
      push_neg at h
      -- Now proving that if contradiction is assumed $y >2.5$, which would filtered through the whole proof
      have h1 : log x ^ 2 + 2 * log x + 2 > 0 := by
        nlinarith [sq_nonneg (log x + 1)]
        all_goals norm_num
        <;> try tauto
        all_goals linarith
      have h2 : (log x * (2 * log x) + 3 * log x + 3) > (2.5) * (log x ^ 2 + 2 * log x + 2) := by
        have h' : (log x * (2 * log x) + 3 * log x + 3) / (log x ^ 2 + 2 * log x + 2) > (2.5 : ℝ) := by
          linarith
        have h_pos : log x ^ 2 + 2 * log x + 2 ≠ 0 := by
          nlinarith [sq_nonneg (log x + 1)]
        apply (lt_div_iff₀' (by nlinarith)).mp at h'
        linarith
        all_goals norm_num
        <;> try tauto
        all_goals linarith
      ring_nf at h2
      nlinarith [sq_nonneg (log x + 2), sq_nonneg (log x + 1), sq_nonneg (log x - 1)]
      all_goals norm_num
      all_goals try tauto
      all_goals linarith
  · -- Now need to show existence of $x$ for which $f(x) = 2.5$
    use (Real.exp (-2 : ℝ))
    constructor
    · -- Now need to show $f(e^{-2}) = 2.5$
      rw [hf]
      have h0 : log (Real.exp (-2 : ℝ)) = -2 := by
        simp [Real.log_exp]
      have h1 : log ((Real.exp (-2 : ℝ) ) ^ 2) = -4 := by
        calc
          log ((Real.exp (-2 : ℝ) ) ^ 2) = 2 * log (Real.exp (-2 : ℝ)) := by
            simp [log_pow]
          _ = 2 * (-2) := by
            rw [h0]
          _ = -4 := by norm_num
      have h2 : log ((Real.exp (-2 : ℝ) ) ^ 3) = -6 := by
        calc
          log ((Real.exp (-2 : ℝ) ) ^ 3) = 3 * log (Real.exp (-2 : ℝ)) := by
            simp [log_pow]
          _ = 3 * (-2) := by
            rw [h0]
          _ = -6 := by norm_num
      simp only [h0, h1, h2]
      norm_num
      <;> simp [h0, h1, h2]
      <;> norm_num
      <;> try tauto
      all_goals norm_num
      all_goals try tauto
      all_goals linarith
    · -- Now need to show $e^{-2} > 0$
      positivity
      all_goals try tauto
      all_goals norm_num
      all_goals try positivity
      all_goals linarith