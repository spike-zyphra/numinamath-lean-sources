import Mathlib

theorem number_theory_171417 (z : ℕ) (hz : z ∈ Finset.Icc 1000 9999) :
    24 ∣ z ∧ (z / 100) % 10 = 1 ∧ (z / 10) % 10 = 3 ↔ z = 2136 ∨ z = 5136 ∨ z = 8136 := by
  rw [Finset.mem_Icc] at hz
  constructor
  · -- Forward direction: If z is a four-digit number divisible by 24 with the given digits, then z is in the set {2136, 5136, 8136}
    intro h
    rcases h with ⟨h24, h1, h3⟩
    rcases hz with ⟨hz1, hz2⟩
    interval_cases z <;> norm_num at h24 h1 h3 ⊢ <;> omega
  · -- Backward direction: If z is in {2136, 5136, 8136}, then it's a four-digit number divisible by 24 with digits 1 and 3 at the second and third positions.
    rintro (rfl | rfl | rfl)
    · -- Show that 2136 satisfies all the conditions
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Show that 5136 satisfies all the conditions
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Show that 8136 satisfies all the conditions
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num