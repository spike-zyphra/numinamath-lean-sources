import Mathlib

open Finset Real

theorem negated_number_theory_68840 (p : ℕ → ℕ)
    (hp : ∀ n, Odd (p n) ∧ p n ∣ n ∧ ∀ m, m ∣ n → Odd m → m ≤ p n) :
    (∑ k ∈ Icc 1 (2 ^ n), p k / k : ℝ) / 2 ^ n > 2 / 3 := by
  have h1 := hp 0
  have hp0 := h1.1
  have hp1 := h1.2.1
  have hp2 := h1.2.2
  have h2 := hp2 (p 0 + 2)
  have h3 : p 0 + 2 ∣ (0 : ℕ) := by 
    simp
  have h4 : Odd (p 0 + 2) := by 
    have hp0_odd : Odd (p 0) := hp0
    rcases hp0_odd with ⟨k, hk⟩
    use k + 1
    all_goals 
      omega
  have h5 : p 0 + 2 ≤ p 0 := by 
    specialize h2 h3 h4
    linarith
  all_goals 
    omega