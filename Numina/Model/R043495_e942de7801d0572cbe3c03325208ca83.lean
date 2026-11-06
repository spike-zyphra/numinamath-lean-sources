import Mathlib

lemma lemma_1 (p : ℕ) (hp : Odd p) : 4 ∣ (3^p + 1) ∧ ¬8 ∣ (3^p + 1) := by
  have h1 : p % 2 = 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  have h2 : (3 ^ p + 1) % 4 = 0 := by
    have h3 : p % 2 = 1 := h1
    have h4 : (3 ^ p) % 4 = 3 := by
      have h5 : ∀ k : ℕ, (3 ^ (2 * k + 1) : ℕ) % 4 = 3 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          all_goals
            omega
      obtain ⟨k, hk⟩ := hp
      have h7 : p = 2 * k + 1 := by
        omega
      rw [h7]
      apply h5 k
    omega
  have h5 : (3 ^ p + 1) % 8 = 4 := by
    have h11 : p % 2 = 1 := h1
    have h7 : (3 ^ p) % 8 = 3 := by
      have h8 : ∀ k : ℕ, (3 ^ (2 * k + 1) : ℕ) % 8 = 3 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          <;> ring_nf at ih ⊢
          <;> norm_num [Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals
            omega
      obtain ⟨k, hk⟩ := hp
      have h7 : p = 2 * k + 1 := by
        omega
      rw [h7]
      apply h8 k
    omega
  constructor
  · 
    omega
  · 
    omega


theorem number_theory_182991 (p : ℕ) (hp : p > 1) : ¬(2^p ∣ 3^p + 1) := by
  by_contra h
  have h3 : p ≥ 2 := by omega
  by_cases h4 : p % 2 = 1
  · 
    have h5 : Odd p := by
      exact ⟨(p - 1) / 2, by omega⟩
    have h6 := lemma_1 p h5
    have h7 : 2 ^ p ∣ 3 ^ p + 1 := by
      simpa using h
    have h8 : p ≥ 3 := by
      by_contra h
      push_neg at h
      have : p < 3 := by omega
      interval_cases p <;> norm_num at h4 h7 h
    have h9 : (3 ^ p + 1) % 8 = 4 := by 
      omega
    have h10 : 2 ^ 3 ∣ 2 ^ p := by
      exact pow_dvd_pow _ (by omega)
    have h11 : 2 ^ 3 ∣ 3 ^ p + 1 := by
      exact dvd_trans h10 h7
    have h12 : (3 ^ p + 1) % 8 = 0 := by
      omega
    omega
  · 
    have h4' : p % 2 = 0 := by omega
    have h7 : 2 ^ p ∣ 3 ^ p + 1 := by
      simpa using h
    have h8 : p ≥ 2 := by omega
    have h9 : (3 ^ p + 1) % 4 = 2 := by
      have h9 : ∀ k : ℕ, (3 ^ (2 * k) + 1) % 4 = 2 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          all_goals
            omega
      have h10 : ∃ k, p = 2 * k := by 
        refine' ⟨p / 2, by omega⟩
      rcases h10 with ⟨k, hk⟩
      rw [hk]
      apply h9 k
    have h10 : (3 ^ p + 1) % 4 = 0 := by
      have h11 : 2^2 ∣ 3 ^ p + 1 := by
        have h8 : 2^2 ∣ 2^p := by 
          exact pow_dvd_pow _ (by omega)
        have h9 : 2 ^ p ∣ 3 ^ p + 1 := by
          simpa using h
        exact dvd_trans h8 h9
      omega
    omega