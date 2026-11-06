import Mathlib

theorem number_theory_144391 (p : ℕ) (hp : Nat.Prime p) (h : 5 ≤ p) :
    24 ∣ (p^2 - 1) := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h3 : ¬ Nat.Prime p := by
      have h4 : p > 2 := by linarith
      have h5 : p % 2 = 0 := by linarith
      have h6 : ∃ k, p = 2 * k := by 
        refine' ⟨p / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      have h7 : k > 2 := by nlinarith
      have h8 : ¬ Nat.Prime p := by 
        rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)]
        use 2
        constructor
        · -- Show that 2 divides p
          rw [hk]
          omega
        constructor
        · -- Show that 2 > 1
          norm_num
        · -- Show that 2 < p
          nlinarith
      exact h8
    contradiction
  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h4 : ¬ Nat.Prime p := by
      have h4 : p > 3 := by linarith
      have h5 : p % 3 = 0 := by linarith
      have h6 : ∃ k, p = 3 * k := by 
        refine' ⟨p / 3, by omega⟩
      rcases h6 with ⟨k, hk⟩
      have h7 : k > 1 := by nlinarith
      have h8 : ¬ Nat.Prime p := by 
        rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)]
        use 3
        constructor
        · -- Show that 3 divides p
          rw [hk]
          omega
        constructor
        · -- Show that 3 > 1
          norm_num
        · -- Show that 3 < p
          nlinarith
      exact h8
    contradiction
  have h8 : (p ^ 2) % 8 = 1 := by
    have h1' : p % 2 = 1 := by
      omega
    have h4 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4)
    · -- p ≡ 1 (mod 8)
      simp [Nat.pow_mod, h4]
    · -- p ≡ 3 (mod 8)
      simp [Nat.pow_mod, h4]
    · -- p ≡ 5 (mod 8)
      simp [Nat.pow_mod, h4]
    · -- p ≡ 7 (mod 8)
      simp [Nat.pow_mod, h4]
  have h3 : (p ^ 2) % 3 = 1 := by
    have h5 : p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h5 with (h5 | h5)
    · -- p ≡ 1 (mod 3)
      simp [Nat.pow_mod, h5]
    · -- p ≡ 2 (mod 3)
      simp [Nat.pow_mod, h5]
  -- $24 = \text{LCM}(8, 3)$.
  -- By the Chinese Remainder Theorem, since $p^2 ≡ 1 \pmod{8}$ and $p^2 ≡ 1 \pmod{3}$, we have $p^2 ≡ 1 \pmod{24}$.
  -- Therefore, $24 \mid p^2 - 1$.
  omega