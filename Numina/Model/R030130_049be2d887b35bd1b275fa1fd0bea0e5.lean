import Mathlib

theorem number_theory_266142 (f : ℕ → ℕ)
    (h₀ : ∀ n, Odd n → f n = 1)
    (h₁ : ∀ n, Even n → ∃ k l, n = 2 ^ k * l ∧ Odd l ∧ f n = k) :
    IsGreatest {n | ∑ i in Finset.Icc 1 n, f i ≤ 123456} 82307 := by 

  have h2 := h₁ 0 (by decide)
  rcases h2 with ⟨k, l, h_eq, h_odd, h_f⟩
  have h3 : l = 0 := by
    have h4 : (2 ^ k : ℕ) ≥ 1 := by
      have h5 : ∀ k : ℕ, (2 ^ k : ℕ) ≥ 1 := by
        intro k 
        induction k with 
        | zero => 
          simp 
        | succ k ih => 
          simp [pow_add, pow_one] at ih ⊢ 
          all_goals omega 
      specialize h5 k 
      simpa using h5 
    nlinarith [h_eq, h4] 
  have h7 : Odd (0 : ℕ) := by 
    rw [show l = 0 by exact h3] at h_odd 
    exact h_odd 
  have h8 : ¬ Odd (0 : ℕ) := by
    simp [Nat.odd_iff]

  contradiction