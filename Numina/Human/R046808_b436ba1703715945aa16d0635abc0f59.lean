import Mathlib

/- Show that if \( a, b, \) and \( c \) are integers such that \( (a, b) = 1 \) and
  \( c \) divides \( (a + b) \), then \( (c, a) = (c, b) = 1 \). -/
theorem number_theory_4513 {a b c : ℤ}
    (hab : a.gcd b = 1) (hc : c ∣ (a + b)) : c.gcd a = 1 ∧ c.gcd b = 1 := by
  -- gcd(a,b) = gcd(a,a+b)
  have (a b : ℤ) : a.gcd b = a.gcd (a + b) := by
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
  -- Suffices to show `gcd(c,a) | 1` and `gcd(c,b) | 1` .
  suffices c.gcd a ∣ 1 ∧ c.gcd b ∣ 1 by simpa using this
  -- We have `gcd(a,c) | gcd(a,a+b)` because `c | a+b` .
  have h₁ := Int.gcd_dvd_gcd_of_dvd_right a hc
  -- We have `gcd(b,c) | gcd(a,a+b)` because `c | a+b` .
  have h₂ := Int.gcd_dvd_gcd_of_dvd_right b hc
  -- As `gcd(a,a+b) = gcd(a,b) = 1`, we get the desired conclusion.
  rw [← this, hab, Int.gcd_comm] at h₁
  rw [add_comm, ← this, Int.gcd_comm] at h₂
  nth_rw 2 [Int.gcd_comm] at h₂
  rw [hab] at h₂
  exact And.intro h₁ h₂
