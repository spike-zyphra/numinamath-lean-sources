import Mathlib

theorem algebra_297928 : {a : ℝ | ∃b c : ℝ, a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0} = Set.Icc 1 9 := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First, prove the forward direction: if a exists in the set, then 1 ≤ a ≤ 9.
    rintro ⟨b, c, h1, h2⟩
    have h3 : a ^ 2 - 8 * a + 7 = b * c := by
      linarith
    have h5 : b ^ 2 + c ^ 2 = -a ^ 2 + 14 * a - 13 := by
      nlinarith [h3, h2]
    have h6 : (b - c) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h7 : (b - c) ^ 2 = -3 * (a - 1) * (a - 9) := by
      nlinarith [h5, h3]
    have h8 : -3 * (a - 1) * (a - 9) ≥ 0 := by
      nlinarith [h7, h6]
    constructor
    · -- Show that $1 \leq a$
      nlinarith
    · -- Show that $a \leq 9$
      nlinarith
  · -- Now, we need to prove the reverse direction: for each a in [1, 9], there exist b, c satisfying the equations.
    rintro ⟨ha1, ha2⟩
    have h6 : -3 * (a - 1) * (a - 9) ≥ 0 := by 
      nlinarith 
    use (a - 1 + Real.sqrt (-3 * (a - 1) * (a - 9))) / 2, (a - 1 - Real.sqrt (-3 * (a - 1) * (a - 9))) / 2
    constructor 
    · -- First equation
      nlinarith [Real.sqrt_nonneg (-3 * (a - 1) * (a - 9)), Real.sq_sqrt (show (-3 * (a - 1) * (a - 9)) ≥ 0 by nlinarith)]
    · -- Second equation
      nlinarith [Real.sqrt_nonneg (-3 * (a - 1) * (a - 9)), Real.sq_sqrt (show (-3 * (a - 1) * (a - 9)) ≥ 0 by nlinarith)]