import Mathlib

def S : Set ℕ := {n | ∃ m, n = m^2 + m + 1}

theorem number_theory_124210 :
    (∀ n, (n^2 + n + 1) * ((n + 1)^2 + (n + 1) + 1) ∈ S) ∧
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a * b ∉ S := by
  constructor
  · -- First part: show that for all n, the product is in S
    intro n
    use n ^ 2 + 2 * n + 1
    ring_nf
  · -- Second part: provide a counterexample
    use 3, 3
    constructor
    · -- Show that 3 ∈ S
      use 1
      all_goals norm_num
    constructor
    · -- Show that 3 ∈ S
      use 1
      all_goals norm_num
    · -- Show that 3 * 3 ∉ S
      intro h
      rcases h with ⟨m, hm⟩
      have h1 : m ≤ 3 := by
        nlinarith [sq_nonneg (m : ℕ)]
      interval_cases m <;> omega