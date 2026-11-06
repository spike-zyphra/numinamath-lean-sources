import Mathlib

theorem number_theory_291816 : ∀ n : ℕ, n ∈ Finset.Icc 1 511 → ∃ s : Finset ℕ,
    n = ∑ i ∈ s, (2^i : ℕ) := by
  intro n hn
  have h1 : n ≥ 1 := by
    have h2 : n ∈ Finset.Icc 1 511 := hn
    simp at h2 ⊢
    omega
  have h2 : n ≤ 511 := by
    have h2 : n ∈ Finset.Icc 1 511 := hn
    simp at h2 ⊢
    omega
  use (Finset.filter (fun i => (n % (2 ^ (i + 1)) >= 2 ^ i) ) (Finset.range 9))
  interval_cases n <;> native_decide