import Mathlib

theorem number_theory_5647
    (M : Set ℕ)
    (hMub : ∃ a, ∀ m ∈ M, m ≤ a)
    (hMnonempty : M.Nonempty) :
    ∃ m0, ∀ m ∈ M, m ≤ m0 := by
  rcases hMub with ⟨a, ha⟩
  refine ⟨a, fun m hm => ?_⟩
  specialize ha m hm
  exact ha