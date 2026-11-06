import Mathlib

theorem algebra_242461 (x : ℤ) (hx : Odd x) : 48 ∣ x^3 + 3 * x^2 - x - 3 := by
  rcases hx with ⟨k, hk⟩
  have eq : x^3 + 3 * x^2 - x - 3 = 8 * (k^3 + 3 * k^2 + 2 * k) := by
    rw [hk]
    ring_nf
  rw [eq]
  have h1 : (k^3 + 3 * k^2 + 2 * k) % 6 = 0 := by
    have h2 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by
      omega
    rcases h2 with (h | h | h | h | h | h)
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
    ·
      simp [Int.add_emod, Int.mul_emod, h, pow_two, pow_succ, Int.ofNat]
  omega