import Mathlib

theorem number_theory_112389 : ∀ p : Equiv.Perm ℕ, 37 ∣ ∑ i ∈ Finset.Icc 111 999, i * 1000 ^ (p i - 111) := by
  intro p
  have h1 : ∀ i ∈ Finset.Icc 111 999, (i * 1000 ^ (p i - 111) : ℕ) % 37 = i % 37 := by
    intro i hi
    have h2 : ∀ (k : ℕ), (1000 : ℕ) ^ k % 37 = 1 := by
      intro k 
      have h4 : (1000 : ℕ) % 37 = 1 := by norm_num
      have h5 : ∀ (k : ℕ), (1000 : ℕ) ^ k % 37 = 1 := by
        intro k 
        induction k with 
        | zero => 
          simp
        | succ k ih => 
          simp [Nat.pow_succ, Nat.mul_mod, h4, ih]
      exact h5 k 
    have h5 : (1000 ^ (p i - 111) : ℕ) % 37 = 1 := h2 (p i - 111)
    simp [Nat.mul_mod, h5] 
  have h3 : (∑ i in Finset.Icc 111 999, i * 1000 ^ (p i - 111) : ℕ) % 37 = 0 := by 
    have h4 : (∑ i in Finset.Icc 111 999, i * 1000 ^ (p i - 111) : ℕ) % 37 = 0 := by 
      have h5 : (∑ i in Finset.Icc 111 999, i * 1000 ^ (p i - 111) : ℕ) % 37 = 
          (∑ i in Finset.Icc 111 999, (i * 1000 ^ (p i - 111) % 37) ) % 37 := by 
        rw [Finset.sum_nat_mod]
      rw [h5]
      have h6 : ∀ i ∈ Finset.Icc 111 999, (i * 1000 ^ (p i - 111) % 37) = i % 37 := by
        intro i hi
        apply h1 i hi
      rw [Finset.sum_congr rfl (fun i hi => h6 i hi)]
      native_decide
    exact h4
  exact Nat.dvd_of_mod_eq_zero h3