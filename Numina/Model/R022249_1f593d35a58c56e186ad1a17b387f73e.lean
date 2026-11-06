import Mathlib

theorem algebra_130913 (α : ℝ) :
    (∃! xy : ℝ × ℝ, xy.1^2 + xy.2^2 = α ∧ xy.1 = 3 * xy.2) ↔ α = 0 := by
  constructor
  · -- First direction: if exists unique pair then $\alpha = 0$.
    rintro ⟨s, ⟨hs1, hs2⟩, h⟩
    have eq1 : s.1 ^ 2 + s.2 ^ 2 = α := by 
      simpa using hs1 
    have eq2 : α = 10 * (s.2 ^ 2) := by
      have h3 : s.1 = 3 * s.2 := by 
        simpa using hs2
      rw [h3] at eq1 
      linarith
      <;> nlinarith 
    have eq3 : ∀ (y : ℝ × ℝ), ((y.1 ^ 2 + y.2 ^ 2 = α ∧ y.1 = 3 * y.2) ) → y = s := h 
    have eq4 : ((-3 * s.2, -s.2) : ℝ × ℝ) = s := by 
      apply eq3 
      constructor 
      · -- Show that (-3 * s.2)^2 + (-s.2)^2 = α.
        rw [show α = 10 * (s.2 ^ 2) by linarith [eq2]]
        ring_nf 
      · -- Show that -3 * s.2 = 3 * (-s.2).
        ring 
    -- From the equality for the pair, we derive equations for the components.
    have eq5 : (-3 * s.2) = s.1 := by 
      have h1 : ((-3 * s.2, -s.2) : ℝ × ℝ) = s := eq4 
      have eq7 : ((-3 * s.2, -s.2) : ℝ × ℝ).1 = (s : ℝ × ℝ).1 := by 
        rw [h1]
      have eq9 : ((-3 * s.2, -s.2) : ℝ × ℝ).1 = -3 * s.2 := by
        simp 
      have eq10 : (s : ℝ × ℝ).1 = s.1 := by 
        simp 
      rw [eq9] at eq7 
      rw [eq10] at eq7 
      linarith 
    -- Similarly for the second component. 
    have eq6 : (-s.2) = s.2 := by 
      have h1 : ((-3 * s.2, -s.2) : ℝ × ℝ) = s := eq4 
      have eq7 : ((-3 * s.2, -s.2) : ℝ × ℝ).2 = (s : ℝ × ℝ).2 := by 
        rw [h1]
      have eq9 : ((-3 * s.2, -s.2) : ℝ × ℝ).2 = -s.2 := by 
        simp 
      have eq10 : (s : ℝ × ℝ).2 = s.2 := by 
        simp 
      rw [eq9] at eq7 
      rw [eq10] at eq7 
      linarith 
    -- From these equations, we now solve for s.2
    have h6 : s.2 = 0 := by 
      linarith 
    -- From h6, we get that α = 0.
    have h7 : α = (0 : ℝ) := by 
      rw [eq2]
      rw [h6]
      norm_num
    linarith 
  · -- Second, show that $\alpha = 0$ then exists unique pair.
    intro ha
    rw [ha] 
    use (0, 0)
    constructor
    · -- First, show that (0, 0) is a solution.
      norm_num 
    · -- Then, show that any solution is equal to (0, 0).
      intro p hp
      rcases p with ⟨x, y⟩ 
      simp at hp 
      have hx : x = (0 : ℝ) := by 
        nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 0), sq_nonneg (y - 0)]
      have hy : y = (0 : ℝ) := by 
        nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 0), sq_nonneg (y - 0)]
      simp [hx, hy]
      all_goals try { tauto }
      all_goals norm_num <;> nlinarith 
      all_goals norm_num
      all_goals norm_num <;> nlinarith 
      all_goals norm_num
      all_goals norm_num <;> nlinarith