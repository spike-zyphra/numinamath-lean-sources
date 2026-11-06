import Mathlib

/- 1. Prove the following divisibility rule: the number 1207 is divisible by a two-digit number x if and only if the sum of the cubes of the digits of x is 344. -/
theorem number_theory_227688 (x : ℕ) (hx1 : 9 < x) (hx2 : x < 100) :
    x ∣ 1207 ↔ ((Nat.digits 10 x).map (fun i => i^3)).sum = 344 := by
  -- We assert that 17 and 71 are priems
  have p17 : Nat.Prime 17 := by decide
  have p71 : Nat.Prime 71 := by decide
  constructor
  -- If x is a divisor of 1207, then x is either 1, 17, 71, or 1207
  · intro h
    rw [(by norm_num : 1207 = 17 * 71), Nat.dvd_mul] at h
    obtain ⟨a, b, h17, h71, hab⟩ := h
    rw [Nat.dvd_prime p17] at h17
    rw [Nat.dvd_prime p71] at h71
    -- We check the four cases
    rcases h17 with (rfl | rfl)
    · rcases h71 with (rfl | rfl) <;> rw [← hab]; norm_num at hab
      · linarith
      · norm_num
    · rcases h71 with (rfl | rfl) <;> rw [← hab]; norm_num at hab
      · norm_num
      · linarith
  -- If x is a two-digit number, we compute the sum of the cubes of the digits
  · intro h
    have h' : x = 17 ∨ x = 71 := by
      interval_cases x <;> try simp at h
      all_goals decide
    -- It must be either 17 or 71, and both divide 1207
    rcases h' with (rfl | rfl)
    · norm_num
    · norm_num