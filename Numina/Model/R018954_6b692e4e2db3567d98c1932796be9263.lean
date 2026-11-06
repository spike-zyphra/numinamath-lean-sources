import Mathlib

theorem number_theory_326085 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ 2019 ≥ 10 * a ∧ 10 * a ≥ 100 * b ∧ 100 * b ≥ 1000 * c}.ncard = 574 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ 2019 ≥ 10 * a ∧ 10 * a ≥ 100 * b ∧ 100 * b ≥ 1000 * c} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
    (s.1 > 0 ∧ s.2.1 > 0 ∧ s.2.2 > 0 ∧ 2019 ≥ 10 * s.1 ∧ 10 * s.1 ≥ 100 * s.2.1 ∧ 100 * s.2.1 ≥ 1000 * s.2.2
    )) (Finset.Icc (0 : ℕ) 201 ×ˢ Finset.Icc (0 : ℕ) 20 ×ˢ Finset.Icc (0 : ℕ) 2) := by
    ext ⟨a, b, c⟩
    simp
    intro h1 h2 h3 h4 h5 h6
    have h7 : a ≤ 201 := by omega
    have h8 : b ≤ 20 := by omega
    have h9 : c ≤ 2 := by omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide