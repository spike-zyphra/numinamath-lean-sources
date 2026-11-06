import Mathlib

theorem algebra_287622 {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (h : a ≠ 0) :
    ¬∃ x : ℚ, a * x ^ 2 + b * x + c = 0 := by
  rintro ⟨x, hx⟩
  have h1 : (a : ℚ) * x ^ 2 + (b : ℚ) * x + (c : ℚ) = (0 : ℚ) := by
    simpa using hx
  have h2 : ∃ p q : ℤ, q ≠ 0 ∧ x = (p / q : ℚ) ∧ Int.gcd p q = 1 := by
    have h3 : x ∈ ({x | ∃ p q : ℤ, q ≠ 0 ∧ x = (p / q : ℚ) ∧ Int.gcd p q = 1} : Set ℚ) := by
      use (x.num : ℤ), (x.den : ℤ)
      constructor
      · -- Show that the denominator is non-zero
        have h1 : (x.den : ℤ) ≠ 0 := by
          simpa using x.den_ne_zero
        assumption
      constructor
      · -- Show that x = (num / den : ℚ)
        simp [Rat.num_div_den x]
      · -- Show that gcd num den = 1
        have h3 : Int.gcd (x.num : ℤ) (x.den : ℤ) = 1 := by
          exact x.reduced
        assumption
    simpa using h3
  rcases h2 with ⟨p, q, hq, hx', h3⟩
  have h4 : (a : ℚ) * x ^ 2 + (b : ℚ) * x + (c : ℚ) = (0 : ℚ) := h1
  rw [show x = (p / q : ℚ) by linarith [hx']] at h4
  have h5 : a * (p / q : ℚ) ^ 2 + b * (p / q : ℚ) + c = (0 : ℚ) := by
    linarith
  have h6 : a * (p ^ 2 : ℚ) + b * (p * q : ℚ) + c * (q ^ 2 : ℚ) = 0 := by
    have h7 : a * (p / q : ℚ) ^ 2 + b * (p / q : ℚ) + c = (0 : ℚ) := h5
    have h8 : (q : ℚ) ≠ 0 := by
      exact_mod_cast (show q ≠ (0 : ℤ) by assumption)
    have h9 : a * (p ^ 2 : ℚ) + b * (p * q : ℚ) + c * (q ^ 2 : ℚ) = (q ^ 2 : ℚ) * (a * (p / q : ℚ) ^ 2 + b * (p / q : ℚ) + c) := by
      field_simp
      <;> ring
    rw [h9]
    rw [h7]
    norm_num
  have h7 : a * (p ^ 2 : ℤ) + b * (p * q : ℤ) + c * (q ^ 2 : ℤ) = 0 := by
    exact_mod_cast (show a * (p ^ 2 : ℚ) + b * (p * q : ℚ) + c * (q ^ 2 : ℚ) = (0 : ℚ) by linarith [h6])
  have h8 : a % 2 = 1 := by
    obtain ⟨k, hk⟩ := ha
    omega
  have h9 : b % 2 = 1 := by
    obtain ⟨k, hk⟩ := hb
    omega
  have h10 : c % 2 = 1 := by
    obtain ⟨k, hk⟩ := hc
    omega
  have h11 : (a * p ^ 2 + b * (p * q) + c * q ^ 2 : ℤ) % 2 = 0 := by
    omega
  have h12 : (a * p ^ 2 + b * (p * q) + c * q ^ 2) % 2 = (p ^ 2 + p * q + q ^ 2) % 2 := by
    have h13 : a % 2 = 1 := h8
    have h14 : b % 2 = 1 := h9
    have h15 : c % 2 = 1 := h10
    simp [Int.add_emod, Int.mul_emod, h13, h14, h15]
  rw [h12] at h11
  have h13 : p % 2 = 0 ∨ p % 2 = 1 := by
    omega
  have h14 : q % 2 = 0 ∨ q % 2 = 1 := by
    omega
  rcases h13 with (h13 | h13)
  · -- p is even
    rcases h14 with (h14 | h14)
    · -- q is even
      have h15 : p % 2 = 0 := h13
      have h16 : q % 2 = 0 := h14
      have h19 : (2 : ℤ) ∣ p := by
        omega
      have h20 : (2 : ℤ) ∣ q := by
        omega
      have h21 : Int.gcd p q ≠ 1 := by
        have h22 : (2 : ℤ) ∣ p := h19
        have h23 : (2 : ℤ) ∣ q := h20
        have h24 : (2 : ℤ) ∣ Int.gcd p q := by
          apply Int.dvd_gcd
          · exact h22
          · exact h23
        have h25 : Int.gcd p q ≥ 2 := by
          omega
        have h26 : Int.gcd p q = 1 := h3
        omega
      omega
    · -- q is odd
      have h15 : p % 2 = 0 := h13
      have h16 : q % 2 = 1 := h14
      have h17 : (p ^ 2 + p * q + q ^ 2) % 2 = 1 := by
        simp [Int.add_emod, Int.mul_emod, h15, h16, pow_two]
      omega
  · -- p is odd
    rcases h14 with (h14 | h14)
    · -- q is even
      have h15 : p % 2 = 1 := h13
      have h16 : q % 2 = 0 := h14
      have h17 : (p ^ 2 + p * q + q ^ 2) % 2 = 1 := by
        simp [Int.add_emod, Int.mul_emod, h15, h16, pow_two]
      omega
    · -- q is odd
      have h15 : p % 2 = 1 := h13
      have h16 : q % 2 = 1 := h14
      have h17 : (p ^ 2 + p * q + q ^ 2) % 2 = 1 := by
        simp [Int.add_emod, Int.mul_emod, h15, h16, pow_two]
      omega