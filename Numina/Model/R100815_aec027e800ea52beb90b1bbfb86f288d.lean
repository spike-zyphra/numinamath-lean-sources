import Mathlib

theorem number_theory_264748 :
    Set.ncard {p : ℕ × ℕ | p.1 * p.2 % 3 = 0 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 86} = 2002 := by 
  have h1 : {p : ℕ × ℕ | p.1 * p.2 % 3 = 0 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 86} = Finset.filter (fun p => p.1 * p.2 % 3 = 0 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 86) (Finset.Icc (0 : ℕ) 86 ×ˢ Finset.Icc (0 : ℕ) 86) := by
    ext ⟨a, b⟩
    simp
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide