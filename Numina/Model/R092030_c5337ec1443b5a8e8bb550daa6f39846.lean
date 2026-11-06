import Mathlib

theorem algebra_10382 : IsLeast {x | ∃a : ℝ, x = 2*a + 1 ∧ 6*a^2 + 5*a + 4 = 3} 0 := by
  constructor
  · -- Let's verify 0 is in the set
    use -1 / 2
    norm_num
  · -- Now we prove 0 is the smallest
    intro y hy
    rcases hy with ⟨a, ha1, ha2⟩
    have h1 : 6 * a^2 + 5 * a + 1 = 0 := by linarith 
    have h2 : (2 * a + 1) * (3 * a + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case where 2a + 1 = 0
      linarith [ha1, h3]
    · -- Case where 3a + 1 = 0
      have ha3 : a = -1 / 3 := by
        linarith 
      rw [ha3] at ha1 
      nlinarith