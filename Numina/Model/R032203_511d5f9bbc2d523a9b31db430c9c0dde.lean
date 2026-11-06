import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_291293 {E F : Set ℝ}
  (hE : E = {x | ∃ n : ℤ, x = cos (n * π / 3)}) (hF : F = {x | ∃ m : ℤ, x = sin ((2 * m - 3) * π / 6)}) :
  E = F := by

  ext x 
  simp [hE, hF]
  constructor
  · -- Assume x ∈ E, need to show x ∈ F 
    rintro ⟨n, hn⟩ 
    use n + 3
    have h1 : sin ((2 * (n + 3 : ℤ) - 3) * π / 6) = cos (n * π / 3) := by
      have h2 : sin ((2 * (n + 3 : ℤ) - 3) * π / 6) = sin (n * π / 3 + π / 2) := by 
        have h3 : (2 * (n + 3 : ℤ) - 3 : ℝ) * π / 6 = n * π / 3 + π / 2 := by 
          field_simp at *
          ring 
        rw [h3]
      have h3 : sin (n * π / 3 + π / 2) = cos (n * π / 3) := by 
        rw [sin_add, sin_pi_div_two, cos_pi_div_two]
        ring 
      rw [h2, h3]
    rw [hn] 
    linarith 
  · -- Assume x ∈ F, need to show x ∈ E 
    rintro ⟨m, hm⟩ 
    use 3 - m 
    have h1 : sin ((2 * (m : ℤ) - 3) * π / 6) = cos ((3 - m : ℤ) * π / 3) := by 
      have h3 : sin ((2 * (m : ℤ) - 3) * π / 6) = cos ( (3 - m : ℤ) * π / 3 ) := by 
        have h9 : sin ((2 * (m : ℤ) - 3) * π / 6) = cos ( 
            Real.pi / 2 - ((2 * (m : ℤ) - 3) * π / 6 ) ) := by 
          rw [← cos_pi_div_two_sub]
        have h10 : Real.pi / 2 - ((2 * (m : ℤ) - 3) * π / 6 ) = 
            ( (3 - m : ℤ) * π / 3 ) := by 
          field_simp at *
          ring 
        rw [h10] at h9 
        linarith 
      linarith 
    rw [hm] 
    linarith