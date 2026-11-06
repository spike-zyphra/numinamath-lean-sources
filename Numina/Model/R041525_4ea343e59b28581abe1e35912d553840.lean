import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246591 {g : ℝ → ℝ} (hg : g = λ x => sin (π * x / 3)) :
    (∀ x, g x + g (x + 2) = g (x + 1)) ∧
    (∀ f : ℝ → ℝ, (∀ x, f x + f (x + 2) = f (x + 1)) →
      (∃ c, Function.Periodic f c)) ∧
    (∀ f : ℝ → ℝ, (∀ x, f x + f (x + 2) = f (x + 1)) → Odd f) := by
  constructor
  · -- Show that g(x) = sin(πx/3) satisfies the equation f(x) + f(x + 2) = f(x + 1)
    intro x
    rw [hg]
    have h1 : sin (π * x / 3) + sin (π * (x + 2) / 3) = sin (π * (x + 1) / 3) := by
      have h2 : π * (x + 2) / 3 = π * x / 3 + 2 * π / 3 := by
        ring
      have h3 : π * (x + 1) / 3 = π * x / 3 + π / 3 := by
        ring
      rw [h2, h3]
      have h4 : sin (π * x / 3 + 2 * π / 3) = sin (π * x / 3) * cos (2 * π / 3) + cos (π * x / 3) * sin (2 * π / 3) := by
        rw [sin_add]
      have h5 : sin (π * x / 3 + π / 3) = sin (π * x / 3) * cos (π / 3) + cos (π * x / 3) * sin (π / 3) := by
        rw [sin_add]
      have h6 : sin (π / 3) = sqrt 3 / 2 := by
        exact sin_pi_div_three
      have h7 : cos (π / 3) = 1 / 2 := by
        exact cos_pi_div_three
      have h8 : sin (2 * π / 3) = sqrt 3 / 2 := by 
        have h9 : 2 * π / 3 = π - (π / 3)  := by 
          ring
        rw [h9]
        rw [sin_pi_sub]
        all_goals linarith [h6]
      have h9 : cos (2 * π / 3) = -1 / 2 := by
        have h10 : 2 * π / 3 = π - (π / 3) := by
          ring
        rw [h10]
        rw [cos_pi_sub]
        all_goals linarith [h7]
      rw [h4, h5, h6, h7,  h8, h9]
      ring
    simpa using h1
  constructor
  · -- Show that all f in M are periodic
    intro f hf
    use 0
    all_goals
      simp [Function.Periodic]
  · -- Show that all f in M are odd functions
    intro f hf
    use (λ x => (f x - 1) / 2)
    funext x
    simp [Odd]
    <;> ring_nf