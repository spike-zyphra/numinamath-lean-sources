import Mathlib
theorem sequence_evaluation (a : ℕ → ℝ)
(a0 : a 0 = 2)
(arec : ∀ n, a (n + 1) = (a n) / (1 + (a n)))
 : a (2012) = 2 / 4025
 :=
by
  have h1 : ∀ (n : ℕ), a n = 2 / (2 * (↑n : ℝ) + 1)
    := by
    intro n
    induction' n with k h'
    · -- Base case: n = 0
      simp [show (↑(0 : ℕ) : ℝ) = (0 : ℝ) by simp, a0]
      <;> ring_nf <;> norm_num
    · -- Inductive step
      have h3 : a (k + 1) = (a k) / (1 + (a k)) := arec k
      rw [h3]
      rw [h']
      field_simp
      ring_nf
      <;> field_simp
      <;> ring
  have h2012 : a 2012 = 2 / (2 * (↑(2012 : ℕ) : ℝ) + 1) := h1 2012
  rw [h2012]
  norm_num