import Mathlib

theorem algebra_300455 (u : ℝ → ℝ → ℝ) (hu : u = fun x y => y^2 - 2 * y + x^2 + 4 * x) :
    IsLeast {z | ∃ x y, z = u x y ∧ 2 * x + y ≥ 1} (-9 / 5) := by 
  constructor 
  · -- Show that -9/5 is indeed attained
    use (-2/5), (9/5)
    constructor
    · -- Show that -9/5 equals u (-2/5) (9/5)
      rw [hu]
      all_goals norm_num
    · -- Show that 2*(-2/5) + 9/5 ≥ 1
      norm_num
  · -- Show that -9/5 is a lower bound
    intro z hz
    rcases hz with ⟨x, y, hz, hxy⟩
    rw [hu] at hz
    simp at hz 
    -- Show that z ≥ -9/5 
    nlinarith [sq_nonneg (y - 9/5), sq_nonneg (x + 2/5), 
        sq_nonneg (y - (1 - 2 * x)), sq_nonneg (x - (-2/5)), sq_nonneg (y - 9/5), 
        hxy]