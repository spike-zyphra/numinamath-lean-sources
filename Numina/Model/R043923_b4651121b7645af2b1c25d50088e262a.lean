import Mathlib

theorem number_theory_308100 (n : ℕ) (A B : ℕ)
    (h₀ : 0 < n) (h₁ : A = ∑ i ∈ Finset.range (2 * n), 4 * 10 ^ i)
    (h₂ : B = ∑ i ∈ Finset.range n, 8 * 10 ^ i) :
    IsSquare (A + 2 * B + 4) := by

  rw [h₁, h₂]
  have h4 : (10 : ℕ) ^ n % 3 = 1 := by
    have h12 : ∀ k : ℕ, (10 : ℕ) ^ k % 3 = 1 := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
        all_goals omega
    exact h12 n

  have h10' : (10 ^ n + 2) % 3 = 0 := by
    omega

  have h12 : (2 * ((10 ^ n + 2) : ℕ) ) % 3 = 0 := by 
    omega

  have h13 : (2 * ((10 ^ n + 2) : ℕ) ) ^ 2 % 9 = 0 := by
    have h14 : (2 * ((10 ^ n + 2) : ℕ) ) % 3 = 0 := h12
    have h17 : ∃ k, (2 * ((10 ^ n + 2) : ℕ) ) = 3 * k := by
      refine' ⟨(2 * ((10 ^ n + 2) : ℕ) ) / 3, by omega⟩
    rcases h17 with ⟨k, hk⟩
    rw [hk]
    ring_nf
    all_goals omega

  have h19 : IsSquare ((∑ i in Finset.range (2 * n), 4 * 10 ^ i) + 2 * (∑ i in Finset.range n, 8 * 10 ^ i) + 4) := by
    have h4' : (∑ i in Finset.range (2 * n), 4 * 10 ^ i) + 2 * (∑ i in Finset.range n, 8 * 10 ^ i) + 4 = ( (2 * ((10 : ℕ) ^ n + 2) ) ^ 2 ) / 9 := by
      have h6 : ∀ (n : ℕ), 0 < n → (∑ i in Finset.range (2 * n), 4 * 10 ^ i) + 2 * (∑ i in Finset.range n, 8 * 10 ^ i) + 4 = ( (2 * ((10 : ℕ) ^ n + 2) ) ^ 2 ) / 9 := by
        intro n hn
        induction n with
        | zero => linarith
        | succ n ih =>
          cases n with
          | zero => norm_num at ih ⊢
          | succ n =>
            simp [Finset.sum_range_succ, pow_two, pow_succ, mul_add, add_mul] at ih ⊢
            ring_nf at ih ⊢
            omega
      exact h6 n h₀

    rw [h4']
    have h17 : ∃ k, (2 * ((10 ^ n + 2) : ℕ) ) = 3 * k := by
      have h14 : (2 * ((10 ^ n + 2) : ℕ) ) % 3 = 0 := h12
      refine' ⟨(2 * ((10 ^ n + 2) : ℕ) ) / 3, by omega⟩

    rcases h17 with ⟨k, hk⟩
    use k
    all_goals
      rw [show (2 * ((10 ^ n + 2) : ℕ) ) = 3 * k by omega]
      ring_nf
      all_goals omega

  exact h19