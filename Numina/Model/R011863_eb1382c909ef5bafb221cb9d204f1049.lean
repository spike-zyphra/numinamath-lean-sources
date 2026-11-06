import Mathlib

theorem negated_number_theory_62669 :
  ¬ ∃ n : ℕ, ∃ k : ℕ, n > 1 ∧ k > 1 ∧ (102^1991 + 103^1991) = n^k := by
  rintro ⟨n, ⟨k, hn, hk, H⟩⟩
  have h1 : n ^ k % 5 = 0 := by
    have h2 : (102 ^ 1991 + 103 ^ 1991) % 5 = 0 := by
      norm_num
    rw [H] at h2
    exact h2
  have h2 : 5 ∣ n ^ k := by omega
  have h3 : 5 ∣ n := by
    apply Nat.Prime.dvd_of_dvd_pow
    norm_num
    exact h2
  have h4 : n % 5 = 0 := by 
    omega
  have h5 : n ^ k % 25 = 0 := by
    have h7 : n % 5 = 0 := h4
    have h8 : n ^ 2 % 25 = 0 := by
      have h9 : n % 5 = 0 := h4
      have h10 : n % 25 = 0 ∨ n % 25 = 5 ∨ n % 25 = 10 ∨ n % 25 = 15 ∨ n % 25 = 20 := by 
        omega
      rcases h10 with (h10 | h10 | h10 | h10 | h10)
      all_goals
        simp [h10, Nat.pow_mod]
    have h10 : k ≥ 2 := by 
      omega
    have h11 : n ^ k % 25 = 0 := by 
      have h12 : n ^ 2 % 25 = 0 := h8
      have h13 : ∀ m : ℕ, n ^ (2 + m) % 25 = 0 := by 
        intro m
        have h14 : n ^ (2 + m) = n^2 * n^m := by ring
        rw [h14]
        simp [Nat.mul_mod, h12]
      have h15 : k ≥ 2 := by omega
      have h16 : k - 2 = k - 2 := by rfl
      have h17 : n ^ k % 25 = 0 := by 
        have h18 : k = 2 + (k - 2) := by omega
        rw [h18]
        apply h13 (k - 2)
      exact h17
    exact h11
  norm_num [H] at h5
  all_goals omega