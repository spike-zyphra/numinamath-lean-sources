import Mathlib

theorem algebra_1153 {n : ℕ} {p : ℝ} (hp : p ≠ 0) : ((-1)^(n + 1) * p^3)^n = p^(3 * n) := by
  have h1 : ((-1 : ℝ) ^ (n + 1) * p ^ 3) ^ n = ((-1 : ℝ) ^ (n + 1)) ^ n * (p ^ 3) ^ n := by
    rw [mul_pow]
  rw [h1]
  have h2 : ((-1 : ℝ) ^ (n + 1)) ^ n = 1 := by
    have h3 : ((-1 : ℝ) ^ (n + 1)) ^ n = (-1 : ℝ) ^ (n * (n + 1)) := by
      rw [← pow_mul]
      all_goals ring_nf
    rw [h3]
    have h4 : (n * (n + 1) : ℕ) % 2 = 0 := by
      have h7 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h7 with (h7 | h7)
      · -- case n is even.
        have h8 : n % 2 = 0 := h7
        simp [Nat.mul_mod, Nat.add_mod, h8]
        all_goals omega
      · -- case n is odd.
        have h8 : n % 2 = 1 := h7
        simp [Nat.mul_mod, Nat.add_mod, h8]
        all_goals omega
    have h5 : ((-1 : ℝ) ^ (n * (n + 1))) = 1 := by
      have h6 : n * (n + 1) % 2 = 0 := h4
      have h7 : (-1 : ℝ) ^ (n * (n + 1)) = 1 := by
        have h9 : (n * (n + 1)) % 2 = 0 := h6
        have h10 : (-1 : ℝ) ^ (n * (n + 1)) = 1 := by
          have h11 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) = 1 := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              simp [pow_add, pow_mul] at ih ⊢
              <;> ring_nf at ih ⊢
              <;> norm_num
              <;> nlinarith [ih]
          have h12 : ∃ k : ℕ, n * (n + 1) = 2 * k := by
            have h13 : (n * (n + 1)) % 2 = 0 := h9
            have h14 : ∃ k : ℕ, n * (n + 1) = 2 * k := by
              refine' ⟨(n * (n + 1)) / 2, by omega⟩
            exact h14
          rcases h12 with ⟨k, hk⟩
          rw [hk]
          specialize h11 k
          simpa using h11
        exact h10
      exact h7
    exact h5
  have h3 : (p ^ 3) ^ n = p ^ (3 * n) := by
    rw [← pow_mul]
    all_goals ring_nf
  rw [h2, h3]
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals ring