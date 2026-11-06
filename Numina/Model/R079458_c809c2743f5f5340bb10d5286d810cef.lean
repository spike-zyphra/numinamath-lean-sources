import Mathlib

theorem number_theory_180994 :
    (Set.ncard {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ (3 ^ p.1 + 7 ^ p.2) % 10 = 8}) / 100 ^ 2 = 3 / 16 := by
  have h1 : {p : ℕ × ℕ | p.1 ∈ Finset.Icc 1 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ (3 ^ p.1 + 7 ^ p.2) % 10 = 8} = Finset.filter (fun p : ℕ × ℕ => (3 ^ p.1 + 7 ^ p.2) % 10 = 8) (Finset.Icc (1 : ℕ) 100 ×ˢ Finset.Icc (1 : ℕ) 100) := by 
    ext ⟨a, b⟩
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide