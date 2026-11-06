import Mathlib

theorem algebra_12342 : {z : ℝ | ∃ a b c, z = a * b + a * c + b * c ∧ a + b + c = 0} = Set.Iic 0 := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_Iic]
  constructor
  · -- First, prove that if there exist a, b, c such that z = ab + ac + bc and a + b + c = 0, then z ≤ 0
    rintro ⟨a, b, c, h_eq, h_sum⟩
    have h1 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by
      ring
    rw [show a + b + c = (0 : ℝ) by linarith] at h1
    have h2 : a^2 + b^2 + c^2 ≥ 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    nlinarith [h_eq, h1, h2]
  
  · -- Proof of reverse direction: For any z ≤ 0, there exist a, b, c such that z = ab + ac + bc and a + b + c = 0
    intro h
    use Real.sqrt (-z), -Real.sqrt (-z), (0 : ℝ)
    constructor
    · -- Show that z = a * b + a * c + b * c
      have h2 : Real.sqrt (-z) ^ 2 = -z := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith [h2, Real.sqrt_nonneg (-z)]
    · -- Show that a + b + c = 0
      linarith [Real.sqrt_nonneg (-z)]
  all_goals linarith