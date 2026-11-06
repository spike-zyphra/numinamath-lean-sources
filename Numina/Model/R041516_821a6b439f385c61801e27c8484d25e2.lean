import Mathlib

theorem algebra_290349 :
    {a : ℝ | ∃ b c, a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0} = Set.Icc 1 9 := by
  ext a 
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor 
  · -- Forward: If exists b, c, the equations hold, then a is in the interval [1, 9].
    intro h
    rcases h with ⟨b, c, h1, h2⟩ 
    constructor
    · -- Prove 1 ≤ a.
      nlinarith [sq_nonneg (b + c), sq_nonneg (b - c), sq_nonneg (a - 1), sq_nonneg (a - 9)]
    · -- Prove a ≤ 9.
      nlinarith [sq_nonneg (b + c), sq_nonneg (b - c), sq_nonneg (a - 1), sq_nonneg (a - 9)]
 
  · -- Backward: If a is in the interval [1, 9], then there exist b and c.
    rintro ⟨ha1, ha2⟩
    use ((a - 1) + Real.sqrt (-3 * a ^ 2 + 30 * a - 27)) / 2, ((a - 1) - Real.sqrt (-3 * a ^ 2 + 30 * a - 27)) / 2
    constructor
    · -- Check the first equation: a^2 - b*c -8*a +7 = 0
      have h11 : 0 ≤ -3 * a ^ 2 + 30 * a - 27 := by 
        nlinarith 
      have h12 : Real.sqrt (-3 * a ^ 2 + 30 * a - 27) ^ 2 = -3 * a ^ 2 + 30 * a - 27 := by 
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [Real.sqrt_nonneg (-3 * a ^ 2 + 30 * a - 27)]
  
    · -- Check the second equation: b^2 +c^2 +b*c -6*a +6=0
      have h11 : 0 ≤ -3 * a ^ 2 + 30 * a - 27 := by 
        nlinarith 
      have h12 : Real.sqrt (-3 * a ^ 2 + 30 * a - 27) ^ 2 = -3 * a ^ 2 + 30 * a - 27 := by 
        rw [Real.sq_sqrt]
        nlinarith 
      nlinarith [Real.sqrt_nonneg (-3 * a ^ 2 + 30 * a - 27)]