import Mathlib

theorem number_theory_177951 :
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ 2017 ≥ 10 * a ∧ 10 * a ≥ 100 * b ∧ 100 * b ≥ 1000 * c}.ncard = 574 := by 
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ 2017 ≥ 10 * a ∧ 10 * a ≥ 100 * b ∧ 100 * b ≥ 1000 * c} = Finset.filter (fun s => 
    0 < s.1 ∧ 0 < s.2.1 ∧ 0 < s.2.2 ∧ 2017 ≥ 10 * s.1 ∧ 10 * s.1 ≥ 100 * s.2.1 ∧ 100 * s.2.1 ≥ 1000 * s.2.2
  ) (Finset.Icc (0 : ℕ) 201 ×ˢ Finset.Icc (0 : ℕ) 201 ×ˢ Finset.Icc (0 : ℕ) 2) := by
    ext ⟨a, b, c⟩
    simp 
    intro h1 h2 h3 h4 h5 h6 
    have h7 : a ≤ 201 := by linarith 
    have h8 : b ≤ 201 := by linarith 
    have h9 : c ≤ 2 := by linarith 
    simp [h7, h8, h9]
    all_goals tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide