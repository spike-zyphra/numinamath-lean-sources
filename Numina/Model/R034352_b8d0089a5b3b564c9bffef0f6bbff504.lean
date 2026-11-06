import Mathlib

theorem number_theory_8083 (n : ℕ) (h : 1 < n) :
    ¬ ∃ m, m^2 = ∑ i ∈ Finset.range n, 10^i := by
  rintro ⟨m, hm⟩
  have h1 : m ^ 2 = ∑ i in Finset.range n, 10 ^ i := hm
  have h2 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Nat.mul_mod, h1]
  have h3 : ∀ k : ℕ, k ≥ 2 → (∑ i in Finset.range k, 10 ^ i) % 4 = 3 := by
    intro k hk
    have base2 : (∑ i in Finset.range 2, 10 ^ i) % 4 = 3 := by 
      norm_num [Finset.sum_range_succ]
    have step : ∀ k' : ℕ, k' ≥ 2 → (∑ i in Finset.range k', 10 ^ i) % 4 = 3 → (∑ i in Finset.range (k' + 1), 10 ^ i) % 4 = 3 := by 
      intro k' h_kprime_ge_2 h
      have eq1 : (∑ i in Finset.range (k' + 1), 10 ^ i) = (∑ i in Finset.range k', 10 ^ i) + 10 ^ k' := by 
        rw [Finset.sum_range_succ]
      have eq2 : (10 ^ k') % 4 = 0 := by
        have h1 : k' ≥ 2 := h_kprime_ge_2
        have h3 : ∀ (x : ℕ), (10 : ℕ) ^ (x + 2) % 4 = 0 := by
          intro x 
          induction x with
          | zero => 
            norm_num
          | succ x ih =>
            simp [pow_succ, Nat.mul_mod] at ih ⊢ 
            <;> omega
        specialize h3 (k' - 2)
        have h4 : k' - 2 + 2 = k' := by 
          omega
        rw [h4] at h3
        omega
      rw [eq1]
      omega
    exact Nat.le_induction base2 step k hk
  have h4 : n ≥ 2 := by 
    omega
  have h10 : (∑ i in Finset.range n, 10 ^ i) % 4 = 3 := h3 n h4
  have h5 : m ^ 2 % 4 = 3 := by 
    omega
  omega