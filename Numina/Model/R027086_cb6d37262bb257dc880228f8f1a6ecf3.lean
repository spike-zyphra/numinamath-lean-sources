import Mathlib

theorem number_theory_6405 (m n : ℕ) :
    2^m = 6 * n + 2 ↔ ∃ k, (m, n) = (2 * k + 1, (2^(2 * k) - 1) / 3) := by
  constructor
  · -- Assume 2^m = 6 * n + 2, prove there exists k such that (m, n) = (2 * k + 1, (2^(2 * k) - 1) / 3)
    intro h
    have h1 : m > 0 := by
      by_contra h1
      push_neg at h1
      have h2 : m = 0 := by linarith
      rw [h2] at h
      norm_num at h
    -- show m is odd
    have h2 : m % 2 = 1 := by
      by_contra h2
      push_neg at h2
      have h3 : m % 2 = 0 := by 
        omega
      have h4 : ∃ k, m = 2 * k := by 
        refine' ⟨m / 2, by omega⟩
      rcases h4 with ⟨k, h5⟩
      have eq1 : 2 ^ m = 2 * (3 * n + 1) := by 
        omega
      rw [h5] at eq1
      have h6 : (2 ^ (2 * k) : ℕ) % 3 = 1 := by 
        have h1 : ∀ k : ℕ, (2 ^ (2 * k) : ℕ) % 3 = 1 := by 
          intro k 
          induction k with
          | zero =>
            simp 
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
            omega 
        have h2 := h1 k 
        omega 
      have h7 : (2 ^ (2 * k) : ℕ) % 3 = 2 := by 
        omega
      omega 
    -- use m is odd to complete the proof
    have h3 : ∃ k, m = 2 * k + 1 := by 
      refine' ⟨(m - 1) / 2, by 
        have h4 : m % 2 = 1 := h2
        have h5 : m ≥ 1 := by omega 
        omega 
      ⟩
    rcases h3 with ⟨k, hk⟩
    have h4 : n = (2 ^ (2 * k) - 1) / 3 := by 
      have eq1 : 2 ^ m = 2 * (3 * n + 1) := by 
        omega 
      rw [show m = 2 * k + 1 by omega] at eq1
      have eq2 : (2 : ℕ) ^ (2 * k + 1) = 2 * (3 * n + 1) := eq1 
      have eq3 : (2 : ℕ) ^ (2 * k + 1) = 2 * ((2 : ℕ) ^ (2 * k) ) := by 
        ring_nf 
      have eq4 : (2 : ℕ) ^ (2 * k) = 3 * n + 1 := by 
        omega 
      omega 
    exact ⟨k, by simp [Prod.ext_iff, hk, h4]⟩ 
  · -- Assume ∃ k, (m, n) = (2 * k + 1, (2^(2 * k) - 1) / 3)
    rintro ⟨k, hk⟩
    rcases Prod.mk.inj_iff.mp hk with ⟨rfl, rfl⟩
    have eq1 : (2 : ℕ) ^ (2 * k + 1) = 2 * ((2 : ℕ) ^ (2 * k)) := by 
      ring_nf 
    have eq2 : (2 : ℕ) ^ (2 * k) = 3 * (( (2 ^ (2 * k) - 1) / 3) ) + 1 := by 
      have h1 : ((2 ^ (2 * k) : ℕ) ) % 3 = 1 := by 
        have h2k : ∀ k : ℕ, (2 ^ (2 * k) : ℕ) % 3 = 1 := by 
          intro k 
          induction k with 
          | zero => 
            simp 
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
            omega 
        have h2 := h2k k 
        omega 
      have h4 : 3 * (( (2 ^ (2 * k) - 1) / 3) ) = (2 ^ (2 * k) - 1) := by 
        omega 
      omega 
    have h5 : (2 : ℕ) ^ (2 * k + 1) = 6 * (( (2 ^ (2 * k) - 1) / 3) ) + 2 := by 
      rw [eq1]
      rw [eq2]
      <;> ring_nf <;> omega
    linarith [h5]