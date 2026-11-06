import Mathlib

theorem number_theory_188317 (a b c d m : ℤ) (h : 5 ∣ a * m^3 + b * m^2 + c * m + d)
    (hd : ¬5 ∣ d) : ∃ n : ℤ, 5 ∣ d * n^3 + c * n^2 + b * n + a := by
  have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1)
  · -- Assume m % 5 = 0
    have h2 : m % 5 = 0 := h1
    have h3 : (a * m ^ 3 + b * m ^ 2 + c * m + d : ℤ) % 5 = 0 := by
      omega
    -- If m ≡ 0 (mod 5), then $a m^3 + b m^2 + c m + d \equiv d \equiv 0 \pmod{5}$, hence 5 divides $d$, contradicts with $hd$
    have h4 : d % 5 = 0 := by
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h1] at h3
      omega
    have h5 : 5 ∣ d := by
      omega
    contradiction
  · -- Assume m % 5 = 1
    have h2 : m % 5 = 1 := h1
    use 1
    have h4 : (d * (1:ℤ) ^ 3 + c * (1:ℤ) ^ 2 + b * (1:ℤ) + a) % 5 = 0 := by
      have h3 : (a * m ^ 3 + b * m ^ 2 + c * m + d : ℤ) % 5 = 0 := by
        omega
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2] at h3 ⊢
      omega
    exact Int.dvd_of_emod_eq_zero h4
  · -- Assume m % 5 = 2
    have h2 : m % 5 = 2 := h1
    use 3
    have h4 : (d * (3:ℤ) ^ 3 + c * (3:ℤ) ^ 2 + b * (3:ℤ) + a) % 5 = 0 := by
      have h3 : (a * m ^ 3 + b * m ^ 2 + c * m + d : ℤ) % 5 = 0 := by
        omega
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2] at h3 ⊢
      omega
    exact Int.dvd_of_emod_eq_zero h4
  · -- Assume m % 5 = 3
    have h2 : m % 5 = 3 := h1
    use 2
    have h4 : (d * (2:ℤ) ^ 3 + c * (2:ℤ) ^ 2 + b * (2:ℤ) + a) % 5 = 0 := by
      have h3 : (a * m ^ 3 + b * m ^ 2 + c * m + d : ℤ) % 5 = 0 := by
        omega
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2] at h3 ⊢
      omega
    exact Int.dvd_of_emod_eq_zero h4
  · -- Assume m % 5 = 4
    have h2 : m % 5 = 4 := h1
    use 4
    have h4 : (d * (4:ℤ) ^ 3 + c * (4:ℤ) ^ 2 + b * (4:ℤ) + a) % 5 = 0 := by
      have h3 : (a * m ^ 3 + b * m ^ 2 + c * m + d : ℤ) % 5 = 0 := by
        omega
      simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod, h2] at h3 ⊢
      omega
    exact Int.dvd_of_emod_eq_zero h4