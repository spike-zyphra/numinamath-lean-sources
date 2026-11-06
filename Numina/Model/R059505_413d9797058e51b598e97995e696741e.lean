import Mathlib

open Real

theorem calculus_23211 {f : ℝ → ℝ} (hf : f = fun x => 1 / sin x - cos (3 * x)) :
    Function.Periodic f (2 * π) := by
  rw [hf]
  intro x
  have h1 : sin (x + 2 * π) = sin x := by
    rw [sin_add_two_pi]
  have h2 : cos (3 * (x + 2 * π)) = cos (3 * x) := by
    have h3 : 3 * (x + 2 * π) = 3 * x + 6 * π := by
      ring
    rw [h3]
    have h4 : cos (3 * x + 6 * π) = cos (3 * x) := by
      have h5 : 3 * x + 6 * π = 3 * x + 3 * (2 * π) := by
        ring
      rw [h5]
      have h6 : cos (3 * x + 3 * (2 * π)) = cos (3 * x) := by
        have h7 : cos (3 * x + 3 * (2 * π)) = cos (3 * x) := by
          have h8 : cos (3 * x + 3 * (2 * π)) = cos (3 * x + (3 : ℕ) * (2 * π)) := by
            ring_nf
          rw [h8]
          rw [cos_add_nat_mul_two_pi]
        exact h7
      exact h6
    exact h4
  simp [h1, h2]
  <;> ring_nf <;> simp [h1, h2]
  all_goals
    try simp [h1, h2]
    <;> try ring_nf <;> simp [h1, h2]
    all_goals
      try linarith [h1, h2]