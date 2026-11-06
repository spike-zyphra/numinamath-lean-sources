import Mathlib

theorem algebra_272412 :
    {(x, y, z) : ℝ × ℝ × ℝ | (x + 1) * (3 - 4 * y) = (6 * x + 1) * (3 - 2 * y) ∧
                             (4 * x - 1) * (z + 1) = (x + 1) * (z - 1) ∧
                             (3 - y) * (z - 2) = (1 - 3 * y) * (z - 6)} =
    {(0, 0, 0), (10/19, 25/7, 25/4)} := by
  ext ⟨x, y, z⟩
  simp [-zero_div]
  constructor
  · -- Forward direction: if (x,y,z) is in the system of equations, it must be one of the two solutions
    rintro ⟨h1, h2, h3⟩
    have eq1 : 15 * x - 8 * x * y + 2 * y = 0 := by
      nlinarith
    have eq2 : 3 * x * z + 5 * x - 2 * z = 0 := by
      nlinarith
    have eq3 : 2 * y * z + 2 * z - 16 * y = 0 := by
      nlinarith
    -- From eq1, solving for y in terms of x
    -- First showing denominator is non-zero
    have h6 : 8 * x - 2 ≠ 0 := by
      by_contra h
      have h5' : 8 * x = 2 := by linarith
      have hx : x = 1 / 4 := by 
        linarith
      rw [hx] at eq1
      nlinarith
    have eq1a : y = 15 * x / (8 * x - 2) := by 
      field_simp [(show 8 * x - 2 ≠ 0 by assumption)]
      linarith
    -- Solving eq3 for z in terms of y
    have h7 : y + 1 ≠ 0 := by
      by_contra h
      have h8 : y = -1 := by
        linarith
      rw [show y = -1 by linarith] at eq3
      nlinarith
    have eq2a : z = 8 * y / (y + 1) := by
      field_simp [(show y + 1 ≠ 0 by assumption)]
      linarith
    -- Substitute eq1a and eq2a into eq2 to solve for x
    rw [show z = 8 * y / (y + 1) by linarith [eq2a] ] at eq2
    rw [show y = 15 * x / (8 * x - 2) by linarith [eq1a] ] at eq2
    field_simp [(show 8 * x - 2 ≠ 0 by assumption), (show y + 1 ≠ 0 by assumption)] at eq2
    ring_nf at eq2
    -- Solving for x
    have h10 : 25 * x * (19 * x - 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h10 ) with h4 h4
    · -- Case x=0
      have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by 
        rw [show x = 0 by linarith] at eq1
        linarith
      have hz0 : z = 0 := by 
        rw [ show y = 0 by linarith] at eq3
        nlinarith
      simp [hx0, hy0, hz0]
    · -- Case x =10/19
      have hx1 : x = 10 / 19 := by linarith
      have hy1 : y = 25 / 7 := by
        rw [show x = 10 / 19 by linarith] at eq1
        linarith
      have hz1 : z = 25 / 4 := by 
        rw [ show y = 25 / 7 by linarith] at eq3
        linarith
      simp [hx1, hy1, hz1]
  · -- Backward: If (x,y,z) is in the set {(0,0,0), (10/19, 25/7, 25/4)}, then it satisfies the system
    intro h
    cases h with
    | inl h_left =>
      rcases h_left with ⟨rfl, rfl, rfl⟩
      norm_num
    | inr h_right =>
      rcases h_right with ⟨rfl, rfl, rfl⟩
      norm_num