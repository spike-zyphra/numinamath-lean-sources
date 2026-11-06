import Mathlib

theorem number_theory_32987 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 7 ∣ (x + 6 * y) * (2 * x + 5 * y) * (3 * x + 4 * y)) :
    343 ∣ (x + 6 * y) * (2 * x + 5 * y) * (3 * x + 4 * y) := by

  have h1 : x % 7 = y % 7 := by 
    have h2 : (x + 6 * y) * (2 * x + 5 * y) * (3 * x + 4 * y) % 7 = 0 := by 
      omega
    have h3 : (x + 6 * y) % 7 = 0 ∨ (2 * x + 5 * y) % 7 = 0 ∨ (3 * x + 4 * y) % 7 = 0 := by 
      by_contra h
      push_neg at h
      have h4 : ((x + 6 * y) * (2 * x + 5 * y) * (3 * x + 4 * y)) % 7 = 
        ((x + 6 * y) % 7) * ((2 * x + 5 * y) % 7) * ((3 * x + 4 * y) % 7) % 7 := by 
        simp [Int.mul_emod]
      rw [h4] at h2
      have h5 : (x + 6 * y) % 7 > 0 := by omega
      have h6 : (x + 6 * y) % 7 < 7 := by omega
      have h7 : (2 * x + 5 * y) % 7 > 0 := by omega
      have h8 : (2 * x + 5 * y) % 7 < 7 := by omega
      have h9 : (3 * x + 4 * y) % 7 > 0 := by omega
      have h10 : (3 * x + 4 * y) % 7 < 7 := by omega
      interval_cases h11 : (x + 6 * y) % 7 <;> interval_cases h12 : (2 * x + 5 * y) % 7 
        <;> interval_cases h13 : (3 * x + 4 * y) % 7 <;> omega

    rcases h3 with (h4 | h5 | h6)
    · -- Case where $x + 6y \equiv 0 \pmod{7}$
      omega
    · -- Case where $2x + 5y \equiv 0 \pmod{7}$
      omega
    · -- Case where $3x + 4y \equiv 0 \pmod{7}$
      omega

  have h3 : 7 ∣ x + 6 * y := by 
    omega

  have h4 : 7 ∣ 2 * x + 5 * y := by 
    omega

  have h5 : 7 ∣ 3 * x + 4 * y := by 
    omega

  -- Each factor is divisible by 7, so the product is divisible by 343
  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h4
  obtain ⟨c, hc⟩ := h5
  use a * b * c
  rw [ha, hb, hc]
  ring