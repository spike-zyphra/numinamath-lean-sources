import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318000 {M N : Set ℝ}
  (hM : M = {x | ∃ m : ℤ, x = sin ((2 * m - 3) * π / 6)})
  (hN : N = {y | ∃ n : ℤ, y = cos (n * π / 3)}) :
  M = N := by
  ext x
  simp only [hM, hN, Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ M, need to show x ∈ N
    rintro ⟨m, hm⟩
    have h1 : sin ((2 * m - 3) * π / 6) = -cos (m * π / 3) := by 
      have h2 : sin ((2 * m - 3) * π / 6) = sin ((m * π / 3) - π / 2) := by 
        ring_nf
      rw [h2]
      have h3 : sin ((m * π / 3) - π / 2) = -cos (m * π / 3) := by 
        rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
        all_goals 
          ring
      linarith [h3]
    use m + 3
    have h4 : sin ((2 * m - 3) * π / 6) = -cos (m * π / 3) := by
      have h2 : sin ((2 * m - 3) * π / 6) = sin ((m * π / 3) - π / 2) := by 
        ring_nf
      rw [h2]
      have h3 : sin ((m * π / 3) - π / 2) = -cos (m * π / 3) := by 
        rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
        all_goals 
          ring
      linarith [h3]
    rw [hm, h4]
    have h5 : -cos (m * π / 3) = cos ((m + 3 : ℤ) * π / 3) := by
      have h3 : (m + 3 : ℤ) * π / 3 = (m * π / 3) + π := by
        field_simp at *
        ring
      rw [h3]
      have h4 : cos ((m * π / 3) + π) = -cos (m * π / 3) := by
        rw [cos_add_pi]
      linarith [h4]
    all_goals linarith [h5]
  · -- Assume x ∈ N, need to show x ∈ M
    rintro ⟨n, hn⟩
    use 3 - n
    have h1 : sin ((2 * (↑(3 - n) : ℤ) - 3) * π / 6) = cos (n * π / 3) := by 
      have h2 : (2 * (↑(3 - n) : ℤ) - 3 : ℝ) * π / 6 = π / 2 - (n * π / 3) := by 
        have h3 : (↑(3 - n : ℤ) : ℝ) = (3 : ℝ) - (↑n : ℝ) := by 
          simp
        rw [h3]
        have h5 : (2 * ((3 : ℝ) - (↑n : ℝ)) - 3 : ℝ) * π / 6 = π / 2 - (n * π / 3) := by 
          field_simp at *
          ring_nf 
        linarith [h5]
      have h4 : sin ((2 * (↑(3 - n) : ℤ) - 3) * π / 6) = sin (π / 2 - (n * π / 3)) := by 
        rw [h2]
      rw [h4]
      have h5 : sin (π / 2 - (n * π / 3)) = cos (n * π / 3) := by 
        rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
        all_goals 
          ring_nf <;> simp
      rw [h5]
    rw [hn]
    rw [h1]