import Mathlib

theorem number_theory_276838 (n : ℕ) (h : Odd n) :
    1956 ∣ 24 * 80^n + 1992 * 83^(n - 1) := by
  rcases h with ⟨k, hk⟩
  have h1 : n = 2 * k + 1 := by
    omega
  rw [h1]
  have eq1 : 24 * 80^(2 * k + 1) + 1992 * 83^(2 * k) = 24 * 80^(2 * k + 1) + 1992 * 83^(2 * k) := by rfl
  have eq2 : ∀ k : ℕ, (24 * 80^(2 * k + 1) + 1992 * 83^(2 * k)) % 1956 = 0 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have eq1 : (24 * 80^(2 * (k + 1) + 1) + 1992 * 83^(2 * (k + 1))) % 1956 =
          (6400 * (24 * 80^(2 * k + 1)) + 6889 * (1992 * 83^(2 * k))) % 1956 := by
        ring_nf
      rw [eq1] at *
      have eq2 : (6400 * (24 * 80^(2 * k + 1)) + 6889 * (1992 * 83^(2 * k))) % 1956 = 0 := by
        have h3 : (24 * 80^(2 * k + 1) + 1992 * 83^(2 * k)) % 1956 = 0 := ih
        have h4 : (6400 * (24 * 80^(2 * k + 1)) + 6889 * (1992 * 83^(2 * k))) % 1956 =
            (6400 * ((24 * 80^(2 * k + 1)) % 1956) + 6889 * ((1992 * 83^(2 * k)) % 1956)) % 1956 := by
          simp [Nat.add_mod, Nat.mul_mod]
        rw [h4]
        have h5 : (24 * 80^(2 * k + 1)) % 1956 = (1956 - (1992 * 83^(2 * k) % 1956)) % 1956 := by
          have h6 : (24 * 80^(2 * k + 1) + 1992 * 83^(2 * k)) % 1956 = 0 := h3
          have h7 : (24 * 80^(2 * k + 1) + 1992 * 83^(2 * k)) % 1956 = (24 * 80^(2 * k + 1) % 1956 + 1992 * 83^(2 * k) % 1956) % 1956 := by
            simp [Nat.add_mod]
          rw [h7] at h6
          omega
        rw [h5]
        all_goals
          omega
      omega
  have eq3 := eq2 k
  have eq4 : 1956 ∣ (24 * 80^(2 * k + 1) + 1992 * 83^(2 * k)) := by
    omega
  simpa using eq4