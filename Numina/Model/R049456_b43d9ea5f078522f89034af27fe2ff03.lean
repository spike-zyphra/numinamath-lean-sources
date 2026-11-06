import Mathlib

theorem number_theory_5631 (n : ℕ) :
    ∃! f : ℕ → ℕ, f 0 = n + 1 ∧ ∀ m, f (m + 1) = (f m + 1) := by 
  use λ m => n + 1 + m
  constructor
  · -- First, we verify that this function satisfies the required conditions
    constructor
    · -- Verify that f_n(0) = n + 1
      simp
    · -- Verify the recurrence relation
      intro m
      simp
      all_goals omega
  · -- Now, we need to show uniqueness
    intro f h
    rcases h with ⟨h0, h1⟩
    funext m
    have h2 : ∀ m : ℕ, f m = n + 1 + m := by
      intro m
      induction m with
      | zero =>
        -- Base case m = 0, then f_n(0) = n + 1
        simp [h0]
      | succ k ihk =>
        -- Assume it holds for k, prove it holds for k + 1
        -- Use the recurrence relation
        have eq1 : f (k + 1) = (f k + 1) := h1 k
        -- Substitute the induction hypothesis
        rw [eq1]
        rw [ihk]
        -- Now need to show that (n + 1 + k) + 1 = n + 1 + (k + 1)
        all_goals simp [add_assoc]
        <;> ring_nf <;> omega
    specialize h2 m
    -- Show that f_n(m) = n + 1 + m
    simpa using h2