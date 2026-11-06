import Mathlib

def Δ (u : ℕ → ℝ) (n : ℕ) := u (n + 1) - u n

theorem algebra_98253 {u : ℕ → ℝ} (hu : ∀ n, u n = n ^ 3 + n) :
    ∀ k, k = 4 → ∀ n, Δ^[k] u n = 0 ∧ ¬(∀ k, k = 3 → ∀ n, Δ^[k] u n = 0) := by 
  intro k hk1 n
  have hu' : ∀ (n : ℕ), u n = n ^ 3 + (n : ℝ) := by
    intro n
    specialize hu n 
    simpa using hu 
  have eq1 : ∀ n : ℕ, Δ u n = 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 2 := by 
    intro n 
    simp [Δ, hu']
    <;> ring_nf 
  have eq2 : ∀ n : ℕ, Δ^[2] u n = 6 * (n : ℝ) + 6 := by 
    intro n 
    simp [Δ, hu', eq1]
    <;> ring_nf 
  have eq3 : ∀ n : ℕ, Δ^[3] u n = (6 : ℝ) := by 
    intro n 
    simp [Δ, hu', eq1, eq2]
    <;> ring_nf 
  have eq4 : ∀ n : ℕ, Δ^[4] u n = (0 : ℝ) := by 
    intro n 
    simp [Δ, hu', eq1, eq2, eq3]
    <;> ring_nf 
  constructor
  · -- Proof that $\Delta^4 u_n = 0$ for all $n$
    have : k = 4 := by 
      exact_mod_cast hk1 
    rw [this]
    exact_mod_cast eq4 n 
  · -- Proof that $\Delta^3 u_n \neq 0$
    have h2 : ∀ n : ℕ, Δ^[3] u n = (6 : ℝ) := eq3
    have h4 : ¬(∀ k, k = 3 → ∀ n, Δ^[k] u n = 0) := by 
      intro h
      specialize h 3 (by rfl)
      specialize h 0 
      have h3 : Δ^[3] u 0 = (6 : ℝ) := h2 0 
      have h1' : Δ^[3] u 0 = (0 : ℝ) := by 
        simpa using h 
      linarith 
    exact_mod_cast h4