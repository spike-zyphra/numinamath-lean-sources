import Mathlib

/- Show that if \( a \) and \( b \) are integers such that \( (a, b) = 1 \), then \( (a+b, a-b) = 1 \) or \( 2 \). -/
theorem number_theory_4507 {a b : ℤ} (hab : a.gcd b = 1) :
    (a + b).gcd (a - b) = 1 ∨ (a + b).gcd (a - b) = 2 := by
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
  -- rewrite `gcd(a+b,a-b)` to `gcd(a+b,2a)`
  rw [this]
  simp only [add_add_sub_cancel, show a + a = 2 * a by omega]
  -- Suffices to show `gcd(a+b,2a) | 2`.
  suffices (a + b).gcd (2 * a) ∣ 2 by
    replace this := And.intro this (show 2 ≠ 0 by norm_num)
    rw [← Nat.mem_divisors, show Nat.divisors 2 = {1, 2} from rfl] at this
    simpa using this
  -- Suffices to show `gcd(2(a+b),2a) | 2`.
  refine Nat.dvd_trans (Int.gcd_dvd_gcd_mul_left _ _ 2) ?_
  simp only [Int.gcd_mul_left, Int.reduceAbs]
  -- Suffices to show `gcd(a+b,a)=1` which can be easily deduced from assumption.
  suffices a.gcd (a + b) = 1 by
    rw [Int.gcd_comm]
    exact ⟨1, by rw [this]⟩
  rwa [← this]
