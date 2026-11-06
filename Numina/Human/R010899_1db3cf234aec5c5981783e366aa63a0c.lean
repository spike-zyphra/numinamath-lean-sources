import Mathlib

/- Chris labels every lattice point in the coordinate plane with the square of the distance from the point to the origin (a lattice point is a point such that both of its coordinates are integers). How many times does he label a point with the number $25$? -/
theorem algebra_22154 : {(x, y) : ℤ × ℤ | x^2 + y^2 = 25}.ncard = 12 := by
  -- It suffices to find out all the lattice points that satisfy x^2 + y^2 = 25
  suffices H : {(x, y) : ℤ × ℤ | x^2 + y^2 = 25} = {(-3, -4), (-3, 4), (-4, -3), (-4, 3), (3, -4), (3, 4), (4, -3), (4, 3), (-5, 0), (5, 0), (0, -5), (0, 5)} by
    rw [H, ← Set.coe_toFinset {(-3, -4), (-3, 4), (-4, -3), (-4, 3), (3, -4), (3, 4), (4, -3), (4, 3), (-5, 0), (5, 0), (0, -5), (0, 5)}, Set.ncard_coe_Finset]
    simp

  -- We prove mutual inclusion
  ext ⟨x, y⟩
  simp
  constructor
  . -- First inclusion
    intro h
    -- We have -5 ≤ x ≤ 5
    have hx1 : x ≥ -5 := by nlinarith
    have hx2 : x ≤ 5 := by nlinarith
    -- Case analysis on x
    interval_cases x
    all_goals
      clear x hx1 hx2
      simp
      norm_num at h
      -- Two goals are trivial
      try
        trivial
      -- Five goals are the form of y = -n ∨ y = n
      try
        rw [Or.comm]
        apply eq_or_eq_neg_of_sq_eq_sq
        linarith
    -- Four goals remain, they are the form: h : a + y^2 = 25, and we need to prove False
    all_goals
        -- Get the value of y^2
        apply eq_sub_of_add_eq' at h
        norm_num at h
        have H : IsSquare (y^2) := ⟨y, pow_two y⟩
        rw [h] at H
        -- But the value of y^2 is not a perfect square, contradiction
        absurd H
        -- The use of native_decide here can be replaced by hand calculation
        native_decide

  . -- Second inclusion
    -- We check all the cases
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      simp
