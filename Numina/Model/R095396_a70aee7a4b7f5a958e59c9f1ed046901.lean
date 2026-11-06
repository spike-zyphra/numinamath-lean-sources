import Mathlib

theorem number_theory_251119 (n : ℕ) (h : Odd n) :
    48 ∣ n^3 + 3 * n^2 - n - 3 := by
  rcases h with ⟨k, hk⟩
  have eq1 : n^3 + 3 * n^2 - n - 3 = 8 * k^3 + 24 * k^2 + 16 * k := by
    rw [hk]
    ring_nf
    <;> omega
  rw [eq1]
  have h4 : (8 * k^3 + 24 * k^2 + 16 * k) % 48 = 0 := by
    have eq2 : 8 * k^3 + 24 * k^2 + 16 * k = 8 * (k * (k + 1) * (k + 2)) := by
      ring_nf
    rw [eq2]
    have h3 : (k * (k + 1) * (k + 2)) % 6 = 0 := by
      have h4 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
      rcases h4 with (h | h | h | h | h | h) <;> simp [Nat.mul_mod, Nat.add_mod, h]
    omega
  exact ⟨ (8 * k^3 + 24 * k^2 + 16 * k) / 48, by omega ⟩