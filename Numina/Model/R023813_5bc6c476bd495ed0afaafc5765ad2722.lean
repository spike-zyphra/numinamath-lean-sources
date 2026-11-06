import Mathlib

theorem number_theory_263593 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ p.1 ^ 2 + p.2 ^ 2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 11 ≤ 1991} = 131 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ p.1 ^ 2 + p.2 ^ 2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 11 ≤ 1991} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ p.1 ^ 2 + p.2 ^ 2 ∧ (p.1 ^ 2 + p.2 ^ 2) / 11 ≤ 1991) (Finset.Icc (0 : ℕ) 148 ×ˢ Finset.Icc (0 : ℕ) 148) := by
    ext ⟨x, y⟩
    simp
    intro hx hy h1 h2
    have h3 : x ≤ 148 := by
      by_contra h
      push_neg at h
      have h4 : x ^ 2 + y ^ 2 > 21901 := by
        have : x ≥ 149 := by linarith
        have : y ≥ 1 := by linarith
        nlinarith
      have h5 : (x ^ 2 + y ^ 2) / 11 > 1991 := by
        omega
      omega
    have h4 : y ≤ 148 := by
      by_contra h
      push_neg at h
      have h5 : x ^ 2 + y ^ 2 > 21901 := by
        have : y ≥ 149 := by linarith
        have : x ≥ 1 := by linarith
        nlinarith
      have h6 : (x ^ 2 + y ^ 2) / 11 > 1991 := by
        omega
      omega
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide