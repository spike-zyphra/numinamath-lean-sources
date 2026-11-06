import Mathlib

theorem algebra_21403 : {a : ℝ | (1 / 5) * abs (9 + 2 * a) < 1} = Set.Ioo (-7) (-2) := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume (1 / 5) * abs (9 + 2 * a) < 1, prove a ∈ (-7, -2)
    intro h
    have h1 : abs (9 + 2 * a) < 5 := by
      linarith
    have h2 : -5 < 9 + 2 * a := by
      linarith [abs_lt.mp h1]
    have h3 : 9 + 2 * a < 5 := by
      linarith [abs_lt.mp h1]
    constructor
    · -- Prove a > -7
      linarith
    · -- Prove a < -2
      linarith
  · -- Assume a ∈ (-7, -2), prove (1 / 5) * abs (9 + 2 * a) < 1
    rintro ⟨h1, h2⟩
    have h3 : -5 < 9 + 2 * a := by 
      linarith
    have h4 : 9 + 2 * a < 5 := by 
      linarith
    have h5 : abs (9 + 2 * a) < 5 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith