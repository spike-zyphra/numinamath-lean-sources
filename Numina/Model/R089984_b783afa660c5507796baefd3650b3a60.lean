import Mathlib

theorem number_theory_10250 :
    (Set.ncard {p : (ℕ × ℕ) | p.1 ∈ Finset.Icc 1 2024 ∧ p.2 ∈ Finset.Icc 1 2024 ∧ (3^p.1 + 7^p.2) % 10 = 8}) / 2024^2 = 3 / 16:= by
  have h1 : {p : (ℕ × ℕ) | p.1 ∈ Finset.Icc 1 2024 ∧ p.2 ∈ Finset.Icc 1 2024 ∧ (3^p.1 + 7^p.2) % 10 = 8} = Finset.filter (fun p => (3^p.1 + 7^p.2) % 10 = 8) (Finset.Icc 1 2024 ×ˢ Finset.Icc 1 2024):= by
    ext ⟨a, b⟩
    simp
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide