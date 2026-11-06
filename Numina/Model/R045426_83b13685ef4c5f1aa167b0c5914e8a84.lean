import Mathlib

theorem number_theory_290108 (n : ℕ) (A B : ℕ)
    (h₀ : 0 < n) (h₁ : A = ∑ i ∈ Finset.range (2 * n), 4 * 10 ^ i)
    (h₂ : B = ∑ i ∈ Finset.range n, 8 * 10 ^ i) :
    IsSquare (A + 2 * B + 4) := by
  rw [h₁, h₂]
  have h4 : ∀ n : ℕ, (∑ i in Finset.range (2 * n), 4 * 10 ^ i : ℕ) + 2 * (∑ i in Finset.range n, 8 * 10 ^ i : ℕ) + 4 = (2 * (10 ^ n + 2)) ^ 2 / 9 := by
    intro n
    induction n with
    | zero => 
      all_goals norm_num
    | succ n ih =>
      simp [Finset.sum_range_succ, mul_add, add_mul] at ih ⊢
      ring_nf at ih ⊢
      all_goals 
        omega 
  have h5' : IsSquare ((∑ i in Finset.range (2 * n), 4 * 10 ^ i : ℕ) + 2 * (∑ i in Finset.range n, 8 * 10 ^ i : ℕ) + 4) := by 
    rw [h4 n]
    have h7 : (2 * (10 ^ n + 2)) % 3 = 0 := by
      have : (10 ^ n) % 3 = 1 := by
        have h10 : ∀ (n : ℕ), (10 : ℕ) ^ n % 3 = 1 := by 
          intro n
          induction n with 
          | zero => 
            simp 
          | succ n ih => 
            simp [pow_succ] at ih ⊢ 
            all_goals omega
        specialize h10 n
        exact h10 
      omega 
    have h8 : 3 ∣ (2 * (10 ^ n + 2) : ℕ) := by 
      omega 
    have h9 : ∃ k : ℕ, 2 * (10 ^ n + 2) = 3 * k := by
      refine ⟨(2 * (10 ^ n + 2)) / 3, by omega⟩
    rcases h9 with ⟨k, hk⟩
    use k 
    have h77 : (2 * (10 ^ n + 2) : ℕ) ^ 2 = 9 * (k ^ 2 : ℕ) := by
      calc 
        (2 * (10 ^ n + 2) : ℕ) ^ 2
          = (3 * k) ^ 2 := by rw [hk]
        _ = 9 * (k ^ 2 : ℕ) := by
          ring 
    have h88 : (2 * (10 ^ n + 2) : ℕ) ^ 2 / 9 = (k ^ 2 : ℕ) := by
      rw [h77]
      all_goals 
        simp [*, Nat.mul_div_cancel] at * <;> omega 
    rw [h88]
    all_goals nlinarith 
  exact h5'