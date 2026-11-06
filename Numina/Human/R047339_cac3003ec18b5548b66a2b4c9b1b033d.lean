import Mathlib

theorem number_theory_187881 :
    Set.ncard {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 1000 ∧ p.2 ∈ Finset.Icc 1 1000 ∧ 5 ∣ p.1^2 + p.2^2} = 360000 := by
  have : {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 1000 ∧ p.2 ∈ Finset.Icc 1 1000 ∧ 5 ∣ p.1^2 + p.2^2} = Finset.filter (λ p => 5 ∣ p.1^2 + p.2^2) (Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000) := by
    ext ⟨x, y⟩
    simp
    tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide