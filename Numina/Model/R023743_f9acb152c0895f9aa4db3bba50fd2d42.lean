import Mathlib

theorem number_theory_249931 {n : ℕ} (hn : n ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (1 / n : ℚ) = 1 / p + 1 / q + 1 / (p * q) ↔ n = 1 := by
  use 2, 3
  constructor
  · -- Assume $2$ is prime ∧ $3$ is prime ∧ $(1/n : ℚ) = 1/2 + 1/3 + 1/(2*3)$, prove $n = 1$
    intro h
    rcases h with ⟨h2, h3, heq⟩
    norm_num at heq
    have h1 : (n : ℚ) = 1 := by
      field_simp at heq ⊢
      nlinarith
    have hn1 : n = 1 := by
      exact_mod_cast h1
    assumption
  · -- Assume $n = 1$, prove $2$ is prime ∧ $3$ is prime ∧ $(1/n : ℚ) = 1/2 + 1/3 + 1/(2*3)$
    intro heq
    rw [heq]
    constructor
    · -- Show 2 is prime
      norm_num
    constructor
    · -- Show 3 is prime
      norm_num
    · -- Show (1/1 : ℚ) = 1/2 + 1/3 + 1/(2*3)
      norm_num