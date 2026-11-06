import Mathlib

theorem number_theory_168871 (z : ℕ) (hz : z ∈ Finset.Icc 100 999) :
    (9 ∣ z ∧ 11 ∣ z) ∧ ((100 * (z % 10) + 10 * ((z / 10) % 10) + (z / 100)) * 9 = 2 * z) ↔
    z = 891 := by
  rw [Finset.mem_Icc] at hz
  constructor
  · -- Forward direction: If z is a 3-digit number divisible by 9 and 11, and swapping its digits gives z' with 9z' = 2z, then z = 891
    intro h
    rcases h with ⟨⟨hz9, hz11⟩, h1⟩
    rcases hz with ⟨hzmin, hzmax⟩
    interval_cases z <;> norm_num at *
  · -- Backward direction: z = 891 satisfies the conditions
    intro hz
    rw [hz]
    constructor
    · -- Show that 9 divides 891 and 11 divides 891
      constructor
      · -- 891 is divisible by 9
        norm_num
      · -- 891 is divisible by 11
        norm_num
    · -- Show that swapping digits and multiplying by 9 gives 2 * 891
      norm_num