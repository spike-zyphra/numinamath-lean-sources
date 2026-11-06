import Mathlib

/-
Prove that amongst any 29 natural numbers there are 15 such that sum of them
is divisible by 15.
-/
theorem number_theory_606104 (s : Finset ℕ) (h : s.card = 29) :
    ∃ t ⊆ s, t.card = 15 ∧ ∑ i ∈ t, i ≡ 0 [MOD 15] := by

  have egz := ZMod.erdos_ginzburg_ziv (n := 15)
    (λ x => x) (s := s) (by linarith)

  obtain ⟨ t, t_in, t_card, t_sum ⟩ := egz
  use t, t_in, t_card

  have := ZMod.natCast_eq_natCast_iff (∑ i ∈ t, (fun x ↦ x) i) 0 15
  simp at this
  rwa [this] at t_sum
