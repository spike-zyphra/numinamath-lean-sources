import Mathlib

theorem algebra_20360 :
    {a : ℝ | ∃ x, x^2 + a * x + 1 = 0 ∧ x ^ 2 - x - a = 0} = {2} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume there exists a common root, prove a = 2
    rintro ⟨x, h1, h2⟩
    have h3 : (a + 1) * (x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case a + 1 = 0, so a = -1
      have ha1 : a = -1 := by linarith
      rw [ha1] at h1 h2
      nlinarith [sq_nonneg (x - 1 / 2)]
    · -- Case x + 1 = 0, so x = -1
      have hx : x = -1 := by linarith
      rw [hx] at h1 h2
      have ha : a = 2 := by
        nlinarith
      linarith
  · -- Assume a = 2, prove there exists a common root
    intro h
    rw [h]
    use -1
    constructor
    · -- Check first equation
      norm_num
    · -- Check second equation
      norm_num