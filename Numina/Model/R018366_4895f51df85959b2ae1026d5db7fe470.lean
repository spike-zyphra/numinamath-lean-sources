import Mathlib

theorem number_theory_94764 :
    {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ 2012 ∧ 5 ^ n < 2 ^ m ∧ 2 ^ m < 2 ^ (m + 2) ∧ 2 ^ (m + 2) < 5 ^ (n + 1)}.ncard = 279 := by 
  have h1 : {(m, n) : ℕ × ℕ | 1 ≤ m ∧ m ≤ 2012 ∧ 5 ^ n < 2 ^ m ∧ 2 ^ m < 2 ^ (m + 2) ∧ 2 ^ (m + 2) < 5 ^ (n + 1)} = Finset.filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 ≤ 2012 ∧ 5 ^ p.2 < 2 ^ p.1 ∧ 2 ^ p.1 < 2 ^ (p.1 + 2) ∧ 2 ^ (p.1 + 2) < 5 ^ (p.2 + 1)) (Finset.Icc (0 : ℕ) 2012 ×ˢ Finset.Icc (0 : ℕ) 867) := by 
    ext ⟨m, n⟩ 
    simp 
    intro h1 h2 h3 h4 h5 
    have h2 : n ≤ 867 := by 
      by_contra h 
      push_neg at h 
      have h6 : n ≥ 868 := by omega 
      have h7 : 5 ^ n ≥ 5 ^ 868 := by 
        apply Nat.pow_le_pow_right 
        all_goals omega 
      have h8 : 2 ^ m ≤ 2 ^ 2012 := by 
        have h9 : m ≤ 2012 := by omega 
        apply Nat.pow_le_pow_right 
        all_goals omega 
      -- Show contradiction: if $5^n < 2^m$ and $5^n \geq 5^{868}$ and $2^m \leq 2^{2012}$.
      -- Need to show $5^{868} > 2^{2012}$ implies that contradiction for pairs.
      have h9 : 5 ^ 868 > 2 ^ 2012 := by 
        norm_num 
      omega 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide