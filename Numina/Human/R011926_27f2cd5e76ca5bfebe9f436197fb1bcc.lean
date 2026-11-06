import Mathlib
/- Consider the sequence $\{a_k\}_{k \geq 1}$ defined by $a_66190 = 1$, $a_66190 = \frac{1}{2}$ and \[ a_{k + 2} = a_k + \frac{1}{2}a_{k + 1} + \frac{1}{4a_ka_{k + 1}}\ \textrm{for}\ k \geq 1. \] Prove that \[ \frac{1}{a_1a_3} + \frac{1}{a_2a_4} + \frac{1}{a_3a_5} + \cdots + \frac{1}{a_{98}a_{100}} < 4. \] -/
theorem inequalities_66190 (a : ℕ → ℝ) (h1 : a 0 = 1) (h2 : a 1 = 1 / 2) (h3 : ∀ k : ℕ, a (k + 2) = a k + (1 / 2) * a (k + 1) + (1 / (4 * a k * a (k + 1)))) : ∑ i ∈ Finset.range 98, (1 / (a i * a (i + 2))) < 4:= by
  -- First, we prove that all terms in the sequence are positive
  -- This is done by induction on k
  have hpos : ∀ k : ℕ, a k > 0 ∧ a (k + 1) > 0:= by
    intro k
    induction k with
    | zero =>
      -- Base case: a(0) > 0 and a(1) > 0
      rw [h1, h2]
      simp
    | succ k ih =>
      -- Inductive step: assuming a(k) > 0 and a(k+1) > 0, prove a(k+1) > 0 and a(k+2) > 0
      rcases ih with ⟨ih1, ih2⟩
      constructor
      .
        exact ih2
      .
        rw [show k + 1 + 1 = k + 2 by omega]
        rw [h3 k]
        positivity

  -- Simplify the previous result to get that all terms are positive
  replace hpos : ∀ k : ℕ, a k > 0:= by
    intro k
    exact (hpos k).1

  -- Key inequality: transform the recurrence relation into a telescoping sum
  -- We show that 1/(a(k)*a(k+2)) ≤ 2/(a(k)*a(k+1)) - 2/(a(k+1)*a(k+2))
  replace h3 : ∀ k : ℕ, 1 / (a k * a (k + 2)) ≤ 2 / (a k * a (k + 1)) - 2 / (a (k + 1) * a (k + 2)):= by
    intro k
    have g1:= hpos k
    have g2:= hpos (k + 1)
    have g3:= hpos (k + 2)
    have g : a k * a (k + 1) * a (k + 2) > 0:= by positivity
    -- Multiply both sides by a(k)*a(k+1)*a(k+2) to simplify the inequality
    suffices 1 / (a k * a (k + 2)) * (a k * a (k + 1) * a (k + 2)) ≤ (2 / (a k * a (k + 1)) - 2 / (a (k + 1) * a (k + 2))) * (a k * a (k + 1) * a (k + 2)) by exact le_of_mul_le_mul_right this g
    rw [show 1 / (a k * a (k + 2)) * (a k * a (k + 1) * a (k + 2)) = a (k + 1) by field_simp ; linarith]
    rw [show (2 / (a k * a (k + 1)) - 2 / (a (k + 1) * a (k + 2))) * (a k * a (k + 1) * a (k + 2)) = 2 * a (k + 2) - 2 * a k by field_simp ; linarith]
    specialize h3 k
    have g4 : 1 / (4 * a k * a (k + 1)) ≥ 0:= by positivity
    linarith

  -- Using the telescoping property to bound the sum
  -- We prove that the sum up to n+1 terms is bounded by 2/(a(0)*a(1)) - 2/(a(n+1)*a(n+2))
  have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), 1 / (a i * a (i + 2)) ≤ 2 / (a 0 * a 1) - 2 / (a (n + 1) * a (n + 2)):= by
    intro n
    induction n with
    | zero =>
      -- Base case: just the first term
      simp
      specialize h3 0
      simp at h3
      exact h3
    | succ n ih =>
      -- Inductive step: add one more term to the sum
      rw [Finset.sum_range_succ]
      specialize h3 (n + 1)
      linarith

  -- Apply the bound to our specific case with n = 97
  specialize h4 97
  rw [show 97 + 1 = 98 by omega] at h4
  rw [show 97 + 2 = 99 by omega] at h4
  have g1:= hpos 98
  have g2:= hpos 99
  rw [h1, h2] at h4
  have g3 : 2 / (a 98 * a 99) > 0:= by positivity
  -- Compute the value of 2/(a(0)*a(1)) = 2/(1*(1/2)) = 4
  rw [show (2 : ℝ) / (1 * (1 / 2)) = 4 by norm_num] at h4
  -- Complete the proof using the fact that 2/(a(98)*a(99)) > 0
  linarith
