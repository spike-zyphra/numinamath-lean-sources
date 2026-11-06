import Mathlib

theorem algebra_5630 : ∃! σ : ℕ → ℕ → ℕ, (∀ n, σ n 0 = n + 1) ∧ (∀ n m, σ n (m + 1) = (σ n m) + 1) := by 
  use fun n => fun m => n + m + 1
  constructor 
  · -- Show that $σ$ satisfies the conditions
    constructor
    · -- Show condition (i) is satisfied: $σ n 0 = n + 1$ for all n.
      intro n
      simp
      <;> ring_nf <;> omega
    · -- Show condition (ii) is satisfied: $σ n (m + 1) = (σ n m) + 1$ for all n m
      intro n m
      simp [add_assoc]
      <;> ring_nf <;> omega
  · -- Show that $σ$ is unique 
    intro σ h 
    rcases h with ⟨h₁, h₂⟩ 
    funext n 
    funext m
    induction m with
    | zero =>
      simp [h₁ n]
      <;> ring_nf <;> omega
    | succ m ih =>
      simp [h₂ n m, ih]
      <;> ring_nf <;> omega