import Mathlib

theorem number_theory_5158 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 7 * p.1 + 11 * p.2 = 2022} = 26 := by 
  have h : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 7 * p.1 + 11 * p.2 = 2022} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ 7 * p.1 + 11 * p.2 = 2022) (Finset.Icc (0 : ℕ) 288 ×ˢ Finset.Icc (0 : ℕ) 183) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide