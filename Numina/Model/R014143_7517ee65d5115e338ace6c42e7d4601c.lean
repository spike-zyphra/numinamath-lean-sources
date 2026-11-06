import Mathlib

theorem number_theory_7233 (n : ℤ) :
    ∃ a b, a^2 - b^2 = n^3 := by 
  use (n^2 + n) / 2
  use (n - n^2) / 2
  -- Show that ((n^2 + n)/2)^2 - (n - n^2)/2)^2 = n^3
  have h1 : ((n ^ 2 + n) / 2 : ℤ) ^ 2 - ((n - n ^ 2) / 2 : ℤ) ^ 2 = n ^ 3 := by
    have h2 : (n ^ 2 + n : ℤ) % 2 = 0 := by
      have h3 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h3 with (h3 | h3)
      · -- Case n is even
        have h4 : n % 2 = 0 := h3
        simp [Int.add_emod, Int.mul_emod, pow_two, h4]
        <;> omega
      · -- Case n is odd
        have h5 : n % 2 = 1 := h3
        simp [Int.add_emod, Int.mul_emod, pow_two, h5]
        <;> omega
    -- Show that (n - n^2) is even
    have h3 : (n - n ^ 2 : ℤ) % 2 = 0 := by
      have h3 : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h3 with (h3 | h3)
      · -- Case n is even
        have h4 : n % 2 = 0 := h3
        simp [Int.sub_emod, Int.mul_emod, pow_two, h4]
        <;> omega
      · -- Case n is odd
        have h5 : n % 2 = 1 := h3
        simp [Int.sub_emod, Int.mul_emod, pow_two, h5]
        <;> omega
    have h5 : ((n ^ 2 + n) / 2 : ℤ) ^ 2 - ((n - n ^ 2) / 2 : ℤ) ^ 2 =
        (((n ^ 2 + n) / 2 : ℤ) - ((n - n ^ 2) / 2 : ℤ)) * (((n ^ 2 + n) / 2 : ℤ) + ((n - n ^ 2) / 2 : ℤ)) := by
      ring
    have h6 : ((n ^ 2 + n) / 2 : ℤ) - ((n - n ^ 2) / 2 : ℤ) = n^2 := by
      have h7 : (n ^ 2 + n : ℤ) % 2 = 0 := h2
      have h8 : (n - n ^ 2 : ℤ) % 2 = 0 := h3
      have h9 : (n ^ 2 + n : ℤ) = 2 * ((n ^ 2 + n) / 2 : ℤ) := by
        omega
      have h10 : (n - n ^ 2 : ℤ) = 2 * ((n - n ^ 2) / 2 : ℤ) := by
        omega
      nlinarith
    have h7 : ((n ^ 2 + n) / 2 : ℤ) + ((n - n ^ 2) / 2 : ℤ) = n := by
      have h7 : (n ^ 2 + n : ℤ) % 2 = 0 := h2
      have h8 : (n - n ^ 2 : ℤ) % 2 = 0 := h3
      have h9 : (n ^ 2 + n : ℤ) = 2 * ((n ^ 2 + n) / 2 : ℤ) := by
        omega
      have h10 : (n - n ^ 2 : ℤ) = 2 * ((n - n ^ 2) / 2 : ℤ) := by
        omega
      nlinarith
    rw [h5, h6, h7]
    <;> nlinarith
    <;> ring_nf
    <;> omega
  linarith [h1]