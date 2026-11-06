import Mathlib

theorem number_theory_135343 (m n : ℕ) :
    ¬ ∃ k, (1 + 3^m + 3^n) = k^2 := by
  rintro ⟨k, hk⟩
  have h1 : k^2 % 8 = 0 ∨ k^2 % 8 = 1 ∨ k^2 % 8 = 4 := by
    have h1 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod]

  have h31 : ∀ m : ℕ, (3 ^ m) % 8 = 1 ∨ (3 ^ m) % 8 = 3 := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
      all_goals omega

  have h2 : (1 + 3 ^ m + 3 ^ n) % 8 = 3 ∨ (1 + 3 ^ m + 3 ^ n) % 8 = 5 ∨ (1 + 3 ^ m + 3 ^ n) % 8 = 7 := by
    have h31m : (3 ^ m) % 8 = 1 ∨ (3 ^ m) % 8 = 3 := h31 m
    have h31n : (3 ^ n) % 8 = 1 ∨ (3 ^ n) % 8 = 3 := h31 n
    omega

  have h3 : k^2 % 8 = (1 + 3 ^ m + 3 ^ n) % 8 := by
    omega

  omega