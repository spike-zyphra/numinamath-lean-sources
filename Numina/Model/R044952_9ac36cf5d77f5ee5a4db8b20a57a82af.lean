import Mathlib

theorem number_theory_4554
    (p n : ℕ) (a : ℕ → ℕ)
    (h₀ : Nat.Prime p)
    (h₁ : 1 ≤ n)
    (h₂ : ∀ i, 1 ≤ i ∧ i ≤ n → a i > 0)
    (h₃ : p ∣ ∏ i in Finset.Icc 1 n, a i):
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ p ∣ a i := by
  have h4 : ∃ i, i ∈ Finset.Icc 1 n ∧ p ∣ a i := by
    have h7 : ∀ (k : ℕ), k ≥ 1 → p ∣ ∏ i in Finset.Icc 1 k, a i → ∃ i, i ∈ Finset.Icc 1 k ∧ p ∣ a i := by
      intro k hk1 hdvd
      induction k with
      | zero =>
        exfalso 
        linarith 
      | succ k ih =>
        cases k with
        | zero =>
          have h8 : p ∣ a 1 := by
            simpa using hdvd
          refine ⟨1, by simp, h8⟩
        | succ k =>
          have h10 : ∏ i in Finset.Icc 1 (k + 1 + 1), a i = (∏ i in Finset.Icc 1 (k + 1), a i) * (a (k + 1 + 1)) := by
            rw [Finset.prod_Icc_succ_top]
            all_goals 
              linarith
          rw [h10] at hdvd 
          cases (Nat.Prime.dvd_mul h₀).mp hdvd with
          | inl h11 =>
            rcases ih (by linarith) h11 with ⟨i, hi, hi1⟩
            refine ⟨i, by simp at hi ⊢; tauto, hi1⟩
          | inr h12 =>
            have h8 : p ∣ a (k + 1 + 1) := by
              simpa using h12
            refine ⟨k + 1 + 1, by simp, h8⟩ 
    have h8 := h7 n (by linarith) h₃
    simpa using h8 
  rcases h4 with ⟨i, hi1, hi2⟩
  have h61 : i ≥ 1 := by 
    simp at hi1 ⊢ 
    all_goals omega
  have h62 : i ≤ n := by
    simp at  hi1 ⊢ 
    all_goals omega 
  refine ⟨i, by omega, by omega, hi2⟩ 
  all_goals linarith