import Mathlib

theorem algebra_230838 :
    {x : ℝ | x^4 - 16 * x^3 + 91 * x^2 - 216 * x + 180 = 0} = 
    {2, 3, 5, 6} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume h : x^4 - 16 * x^3 + 91 * x^2 - 216 * x + 180 = 0, prove h1 : x ∈ {2, 3, 5, 6}
    intro h
    have h1 : x^4 - 16 * x^3 + 91 * x^2 - 216 * x + 180 = (x - 2) * (x - 3) * (x - 5) * (x - 6) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · cases' (mul_eq_zero.mp h2) with h4 h5
      · cases' (mul_eq_zero.mp h4) with h6 h7
        · -- h6 : (x - 2) = 0
          have h8 : x = 2 := by linarith
          simp [h8]
        · -- h7 : (x - 3) = 0
          have h8 : x = 3 := by linarith
          simp [h8]
      · -- h5 : (x - 5) = 0
        have h8 : x = 5 := by linarith
        simp [h8]
    · -- h3 : (x - 6) = 0
      have h8 : x = 6 := by linarith
      simp [h8]
  · -- Assume h1 : x ∈ {2, 3, 5, 6}, prove h : x^4 - 16 * x^3 + 91 * x^2 - 216 * x + 180 = 0
    rintro (h | h | h | h)
    · -- x = 2
      rw [h]
      norm_num
    · -- x = 3
      rw [h]
      norm_num
    · -- x = 5
      rw [h]
      norm_num
    · -- x = 6
      rw [h]
      norm_num