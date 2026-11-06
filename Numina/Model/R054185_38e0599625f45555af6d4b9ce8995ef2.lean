import Mathlib

theorem number_theory_29684 :
    Set.ncard {x : ℕ × ℕ | x.1.Prime ∧ 3 ≤ x.1 ∧ x.1 < 100 ∧ 1 ≤ x.2 ∧ x.2 < x.1 ∧ x.1 ∣ (x.2^(x.1 - 2) - x.2)} = 48 := by
  have h1 : {x : ℕ × ℕ | x.1.Prime ∧ 3 ≤ x.1 ∧ x.1 < 100 ∧ 1 ≤ x.2 ∧ x.2 < x.1 ∧ x.1 ∣ (x.2^(x.1 - 2) - x.2)} = Finset.filter (fun p => (p.1.Prime ∧ 3 ≤ p.1 ∧ p.1 < 100 ∧ 1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 ∣ (p.2^(p.1 - 2) - p.2)) ) (Finset.Icc (0 : ℕ) 99 ×ˢ Finset.Icc (0 : ℕ) 99) := by
    ext ⟨p, a⟩
    simp
    intro h1 h2 h3 h4 h5 h6
    have hp1 : p ≤ 99 := by linarith
    have ha1 : a < 100 := by linarith
    simp [hp1, ha1]
    all_goals omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide