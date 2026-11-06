import Mathlib

theorem number_theory_2204 (m : ℕ) (hm : m > 0) : (2^m + 2^(m + 2006)) % 10 = 0 := by
  have h1 : m ≥ 1 := by linarith
  have h2 : (2^m + 2^(m + 2006)) % 10 = (2^m * (1 + 2^2006)) % 10 := by
    have h3 : 2^m + 2^(m + 2006) = 2^m * (1 + 2^2006) := by
      have h4 : 2^(m + 2006) = 2^m * 2^2006 := by
        ring_nf
      rw [h4]
      all_goals
        ring
    rw [h3]
  rw [h2]

  have h4 : (1 + 2^2006) % 10 = 5 := by
    have h3 : 2^2006 % 10 = 4 := by
      norm_num [Nat.pow_mod]
    omega

  have h8 : 2^m % 2 = 0 := by
    have h9 : m ≥ 1 := by linarith
    have h10 : 2^m % 2 = 0 := by
      have h11 : ∀ (k : ℕ), 2 ^ (k + 1) % 2 = 0 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_succ] at ih ⊢
          all_goals omega
      have h12 : m = (m - 1) + 1 := by
        omega
      rw [h12]
      apply h11 (m - 1)
    omega

  have h16 : (2^m * (1 + 2^2006)) % 10 = 0 := by
    have h11 : (1 + 2^2006) % 10 = 5 := h4
    have h14 : (2^m) % 2 = 0 := h8
    have h19 : ∃ k, 2^m = 2 * k := by
      refine ⟨2 ^ m / 2, by omega⟩
    rcases h19 with ⟨k, hk⟩
    rw [hk]
    have h22 : (2 * k * (1 + 2^2006)) % 10 = 0 := by
      have h11 : (1 + 2^2006) % 10 = 5 := h4
      omega
    omega
  omega