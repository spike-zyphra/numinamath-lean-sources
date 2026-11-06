import Mathlib

theorem number_theory_3818 (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ Finset.Icc 4 22) :
    S.card = 12 → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by 
  intro h1
  have h2 : S.card = 12 := h1
  have h3 : ∀ n ∈ S, 4 ≤ n ∧ n ≤ 22 := by
    intro n hn
    have h4 : n ∈ Finset.Icc 4 22 := hS n hn
    simp at h4 ⊢
    exact h4
  have h4 : S ⊆ (Finset.Icc 4 22) := by
    intro n hn
    have h5 : n ∈ Finset.Icc 4 22 := hS n hn
    exact h5
  have h5 : S ∈ (Finset.powerset (Finset.Icc 4 22)).filter (fun s => s.card = 12) := by
    simp [h4, h2]
  have h6 : ∀ s ∈ (Finset.powerset (Finset.Icc 4 22)).filter (fun s => s.card = 12), 
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a ∣ b := by 
    native_decide
  specialize h6 S h5
  simpa using h6