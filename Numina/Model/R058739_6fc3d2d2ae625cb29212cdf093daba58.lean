import Mathlib

theorem number_theory_12957 {n : ℕ} (hn : n > 0) (h : n % 9 = 7) :
    (3 * n % 9) = 3 := by
  -- Using `simp` with Nat.mul_mod to compute the modular multiplication.
  -- Since n ≡ 7 (mod 9), so 3 * n ≡ 3 * 7 (mod 9)
  -- 3 * 7 = 21, 21 ≡ 3 (mod 9)
  -- Thus, 3 * n ≡ 3 (mod 9)
  simp [Nat.mul_mod, h]
  <;> omega