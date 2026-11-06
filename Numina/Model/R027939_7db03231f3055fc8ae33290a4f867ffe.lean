import Mathlib

theorem number_theory_288964 :
    {(a, b, c) : ℕ × ℕ × ℕ | a.Prime ∧ b.Prime ∧ c.Prime ∧ a < b ∧ b < c ∧ a + b + c = 22}.ncard = 2 := by 
  have : {(a, b, c) : ℕ × ℕ × ℕ | a.Prime ∧ b.Prime ∧ c.Prime ∧ a < b ∧ b < c ∧ a + b + c = 22} = Finset.filter (fun s : ℕ × ℕ × ℕ =>
          (s.1).Prime ∧ (s.2.1).Prime ∧ (s.2.2).Prime ∧ s.1 < s.2.1 ∧ s.2.1 < s.2.2 ∧ s.1 + s.2.1 + s.2.2 = 22) (Finset.Icc (0 : ℕ) 22 ×ˢ Finset.Icc (0 : ℕ) 22 ×ˢ Finset.Icc (0 : ℕ) 22) := by
    ext ⟨a, b, c⟩
    simp
    intro h1 h2 h3 h4 h5 h6
    have h7 : a ≤ 22 := by
      omega
    have h8 : b ≤ 22 := by
      omega
    have h9 : c ≤ 22 := by
      omega
    all_goals tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide