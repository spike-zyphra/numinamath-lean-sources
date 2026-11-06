import Mathlib

/- gcd(a,b) = gcd(a,a+b) -/
lemma gcd_add1 (a b : ℤ) : a.gcd b = a.gcd (a + b) := by
  by_cases ha : a = 0
  · simp [ha]
  · suffices
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + b * y} =
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + (a + b) * y}
    from IsLeast.unique
      (Int.gcd_least_linear ha (b := b))
      (this ▸ Int.gcd_least_linear ha (b := a + b))
    ext n
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    refine fun _ => ⟨fun ⟨x, y, h⟩ => ?_, fun ⟨x, y, h⟩ => ?_⟩
    · use x - y, y; simp [h]; ring
    · use x + y, y; simp [h]; ring

/- Show that if \( k \) is a positive integer, then \( 3k + 2 \) and \( 5k + 3 \) are relatively prime. -/
theorem number_theory_4526 (k : ℤ) : IsCoprime (3 * k + 2) (5 * k + 3) := by
  -- Suffices to show that gcd(3k+2, 5k+3) = 1 .
  rw [Int.isCoprime_iff_gcd_eq_one]
  -- This can be verify by simple calculation.
  rw [
    show 5 * k + 3 = 3 * k + 2 + (2 * k + 1) by omega, ← gcd_add1, Int.gcd_comm,
    show 3 * k + 2 = 2 * k + 1 + (k + 1) by omega, ← gcd_add1, Int.gcd_comm,
    show 2 * k + 1 = k + 1 + k by omega, ← gcd_add1, Int.gcd_comm, ← gcd_add1]
  simp
