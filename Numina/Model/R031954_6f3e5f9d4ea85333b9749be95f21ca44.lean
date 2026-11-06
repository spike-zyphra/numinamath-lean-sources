import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_299066 {E F : Set ℝ}
  (hE : E = {x | ∃ n : ℤ, x = cos (n * π / 3)}) (hF : F = {x | ∃ m : ℤ, x = sin ((2 * m - 3) * π / 6)}) :
  E = F := by 
  rw [hE, hF]
  ext x 
  constructor
  · -- Prove that if x ∈ E, then x ∈ F.
    rintro ⟨n, hn⟩
    use n + 3 
    have h1 : cos (↑n * π / 3) = sin ((2 * ↑(n + 3) - 3) * π / 6) := by
      have h2 : sin ((2 * ↑(n + 3) - 3) * π / 6) = cos (↑n * π / 3) := by 
        have h3 : (2 * ↑(n + 3) - 3) * π / 6 = (↑n * π / 3 + π / 2) := by 
          simp at *
          <;> ring_nf <;> norm_num
        rw [h3]
        have h4 : sin (↑n * π / 3 + π / 2) = cos (↑n * π / 3) := by 
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          all_goals ring 
        linarith [h4]
      linarith [h2]
    rw [hn]
    linarith
  · -- Prove that if x ∈ F, then x ∈ E.
    rintro ⟨m, hm⟩ 
    use m - 3 
    have h1 : sin ((2 * ↑m - 3) * π / 6) = cos (↑(m - 3) * π / 3) := by
      have h2 : sin ((2 * ↑m - 3) * π / 6) = cos (↑(m - 3) * π / 3) := by
        have h3 : sin ((2 * ↑m - 3) * π / 6) = sin ( (↑(m - 3) * π / 3) + π / 2 ) := by
          have h4 : (2 * ↑m - 3) * π / 6 = ( (↑(m - 3) * π / 3) + π / 2 ) := by
            simp at *
            <;> ring_nf 
          rw [h4]
        have h4 : sin ( (↑(m - 3) * π / 3) + π / 2 ) = cos (↑(m - 3) * π / 3) := by
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          all_goals ring
        rw [h3, h4]
      linarith [h2]
    rw [hm] 
    linarith [h1]