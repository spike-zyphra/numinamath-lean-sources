import Mathlib

theorem algebra_13321
  (h0 : a1 = 1) :
  IsLeast {x | ∃(a2 a3 r:ℝ), a2 = a1*r ∧ a3 = a1*r^2 ∧  x = 4 *a2+ 5 * a3} (-4 / 5) := by
    constructor
    · -- First part: prove -4/5 is achievable
      use -2 / 5, 4 / 25, -2 / 5
      constructor
      · -- Verify a2 = a1 * r
        rw [h0]
        norm_num
      constructor
      · -- Verify a3 = a1 * r^2
        rw [h0]
        norm_num
      · -- Verify x = 4*a2 + 5*a3
        norm_num
    · -- Second part: prove -4/5 is a lower bound
      intro x hx
      rcases hx with ⟨a2, a3, r, ha2, ha3, hx_eq⟩
      rw [h0] at ha2 ha3
      have ha2' : a2 = r := by
        linarith
      have ha3' : a3 = r^2 := by
        nlinarith
      rw [hx_eq, ha2', ha3']
      nlinarith [sq_nonneg (r + 2 / 5)]