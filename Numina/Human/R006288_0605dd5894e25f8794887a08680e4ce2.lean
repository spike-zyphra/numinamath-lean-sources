import Mathlib

/- Let $N$ be an integer such that $N \ge 16$ and $N \equiv 16 \pmod{40}$. Let $M$ be a positive integer. Determine the last two digits of $7^{N^M}$. Show the answer is 01. -/
theorem number_theory_635537 (N : ℕ) (hN₀ : 16 ≤ N) (hN₁ : N % 40 = 16) (M : ℕ) (hM₀ : 0 < M) :
    (7 ^ N ^ M) % 100 = 01 := by
  change 7 ^ N ^ M ≡ 1 [MOD 100]
  -- We use the fact that N ≡ 16 [MOD 40] to show that 4 ∣ N ^ M
  obtain ⟨k, hk⟩ : 4 ∣ N ^ M := dvd_pow (by omega) hM₀.ne'
  -- We use the fact that 7 ^ 4 ≡ 1 [MOD 100]
  calc 7 ^ N ^ M
    _ = 7 ^ (4 * k) := by rw [hk]
    _ = (7 ^ 4) ^ k := by rw [pow_mul]
    _ ≡ 1 ^ k [MOD 100] := by gcongr; rfl
    _ = 1 := by simp
