import Mathlib

theorem number_theory_240856 (n : ℕ) (h : Odd n) :
    1947 ∣ 46^n + 296 * 13^n := by
  have h1 : ∀ k : ℕ, 1947 ∣ 46 ^ (2 * k + 1) + 296 * 13 ^ (2 * k + 1) := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 46 ^ (2 * (k + 1) + 1) + 296 * 13 ^ (2 * (k + 1) + 1) =
          46 ^ (2 * k + 1) * 46 ^ 2 + 296 * 13 ^ (2 * k + 1) * 13 ^ 2 := by
        ring_nf
      rw [h2]
      omega
  have h2 : ∃ k : ℕ, n = 2 * k + 1 := by 
    obtain ⟨k, hk⟩ := h
    use k
    all_goals
      linarith
  rcases h2 with ⟨k, hk⟩
  rw [hk]
  apply h1 k