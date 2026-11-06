import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_257418 {M N : Set ℝ}
  (hM : M = {x | ∃ m : ℤ, x = sin ((2*m - 3)*π/6)})
  (hN : N = {y | ∃ n : ℤ, y = cos (n*π/3)}) :
  M = N := by 
  rw [hM, hN]
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, show M ⊆ N
    rintro ⟨m, hm⟩
    use 3 - m 
    have eq1 : sin ((2 * m - 3) * π / 6) = - cos (m * π / 3) := by 
      have h1 : (2 * m - 3) * π / 6 = (m * π / 3) - (Real.pi / 2) := by 
        ring_nf 
        <;> 
        linarith [Real.pi_pos]
      rw [h1]
      rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
      ring
      all_goals linarith 
    have eq2 : - cos (m * π / 3) = cos ((3 - m) * π / 3) := by 
      have h2 : (3 - m) * π / 3 = Real.pi - (m * π / 3) := by 
        ring_nf 
      rw [h2]
      rw [cos_pi_sub]
      <;> ring_nf <;> simp [Real.cos_pi]
    rw [hm, eq1, eq2]
    all_goals norm_cast 
    all_goals linarith 
  · -- Now, show N ⊆ M 
    rintro ⟨n, hn⟩ 
    use 3 - n 
    have h_eq3 : sin ((2 * (3 - ↑n) - 3) * π / 6) = cos (↑n * π / 3) := by 
      have h_eq4 : (2 * (3 - ↑n) - 3) * π / 6 = Real.pi / 2 - (↑n * π / 3) := by 
        ring_nf 
      rw [h_eq4]
      rw [sin_pi_div_two_sub]
      all_goals norm_cast 
    have h_eq4 : sin ((2 * ↑(3 - n) - 3) * π / 6) = sin ((2 * (3 - ↑n) - 3) * π / 6) := by 
      congr 1 
      norm_cast 
      <;> ring_nf <;> norm_num 
    -- Goal is now x = sin ((2 * ↑(3 - n) - 3) * π / 6)
    -- We have x = cos (↑n * π / 3)
    -- So cos (↑n * π / 3) = sin ((2 * ↑(3 - n) - 3) * π / 6)
    -- Now we can use h_eq4 and h_eq3.symm
    rw [show x = cos (↑n * π / 3) by linarith [hn]]
    -- Goal is now cos (↑n * π / 3) = sin ((2 * ↑(3 - n) - 3) * π / 6)
    -- Use h_eq4 to make arguments of sin same.
    rw [show sin ((2 * ↑(3 - n) - 3) * π / 6) = sin ((2 * (3 - ↑n) - 3) * π / 6) by 
          norm_cast 
          <;> ring_nf <;> norm_num
    ]
    -- Goal is now cos (↑n * π / 3) = sin ((2 * (3 - ↑n) - 3) * π / 6)
    -- Now we can use h_eq3.symm to close the goal.
    exact h_eq3.symm
    all_goals norm_cast 
    all_goals ring_nf <;> norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
    all_goals norm_cast 
    all_goals ring_nf <;> norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
    all_goals norm_cast