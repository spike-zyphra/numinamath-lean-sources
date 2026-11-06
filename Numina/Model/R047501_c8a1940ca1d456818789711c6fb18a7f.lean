import Mathlib

theorem algebra_188357 {x y : ℕ} (h1 : 3^(2*x) - 2^y = 725) (h2 : 3^x - 2^(y/2) = 25) :
    x = 3 ∧ y = 2 := by
  have eq1 : 3 ^ (2 * x) ≥ 2 ^ y := by
    omega
  have eq2 : 3 ^ x ≥ 2 ^ (y / 2) := by
    omega
  have h3 : 3 ^ (2 * x) = 2 ^ y + 725 := by
    omega
  have h4 : 3 ^ x = 2 ^ (y / 2) + 25 := by
    omega
  have h5 : y % 2 = 0 := by
    by_contra h
    push_neg at h
    have h6 : y % 2 = 1 := by omega
    have h7 : (2 : ℕ) ^ y % 3 = 2 := by
      have h9 : ∀ k, (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_succ] at ih ⊢
          all_goals omega
      have h10 : ∃ k, y = 2 * k + 1 := by
        refine ⟨(y - 1) / 2, by omega⟩
      rcases h10 with ⟨k, hk⟩
      rw [hk]
      apply h9 k
    have h9 : (3 : ℕ) ^ (2 * x) % 3 = 0 := by
      have h10 : ∀ k > 0, (3 : ℕ) ^ k % 3 = 0 := by
        intro k hk
        induction k with
        | zero => linarith
        | succ k ih =>
          simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
      have h11 : 2 * x > 0 := by
        by_contra h
        push_neg at h
        have : x = 0 := by omega
        rw [this] at h3
        norm_num at h3
      apply h10 (2 * x) 
      omega
    have h10 : (3 : ℕ) ^ (2 * x) % 3 = (2 ^ y + 725) % 3 := by
      omega
    omega
  have h8 : y % 2 = 0 := by omega
  have h11 : ∃ k, y = 2 * k := by
    refine ⟨y / 2, by omega⟩
  rcases h11 with ⟨k, hk⟩
  have h12 : 3 ^ x = 2 ^ k + 25 := by
    have h13 : 2 ^ (y / 2) = 2 ^ k := by
      rw [show y = 2 * k by linarith]
      simp
    rw [h13] at h4
    omega
  have h14 : 3 ^ (2 * x) = 2 ^ (2 * k) + 725 := by
    rw [show y = 2 * k by linarith] at h3
    omega
  have h13 : (3 ^ x : ℕ) ^ 2 = (2 ^ k : ℕ) ^ 2 + 725 := by
    have h15 : 3 ^ (2 * x) = (3 ^ x) ^ 2 := by ring
    rw [h15] at h14
    have h16 : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by ring
    rw [h16] at h14
    omega
  have h14 : 3 ^ x - 2 ^ k = 25 := by
    omega
  have h15 : 3 ^ x + 2 ^ k = 29 := by
    have h16 : (3 ^ x : ℕ) ^ 2 - (2 ^ k : ℕ) ^ 2 = 725 := by
      omega
    have h17 : (3 ^ x : ℕ) ^ 2 = (2 ^ k : ℕ) ^ 2 + 725 := by
      omega
    nlinarith [h14, h17]
  have h18 : (3 : ℕ) ^ x = 27 := by
    have h19 : (2 : ℕ) ^ k = 2 := by
      omega
    omega
  have h21 : x = 3 := by
    have h22 : (3 : ℕ) ^ x = 27 := h18
    have h23 : x = 3 := by
      exact Nat.pow_right_injective (by norm_num) h22
    exact h23
  have h24 : (2 : ℕ) ^ k = 2 := by
    omega
  have h25 : k = 1 := by
    have h26 : (2 : ℕ) ^ k = 2 := h24
    have h27 : k = 1 := by
      exact Nat.pow_right_injective (by norm_num) h26
    exact h27
  have h28 : y = 2 := by
    omega
  exact ⟨h21, h28⟩