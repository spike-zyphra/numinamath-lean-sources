import Mathlib

theorem algebra_235445 :
    {r : ℝ | ∃x y z : ℝ, 
        0 ≤ x ∧ x ≤ Real.pi / 2 ∧ 0 ≤ y ∧ y ≤ Real.pi / 2 ∧ 
        0 ≤ z ∧ z ≤ Real.pi / 2 ∧ Real.sin x = Real.cos y ∧ 
        Real.sin y = Real.cos z ∧ Real.sin z = Real.cos x ∧ 
        r = x + y + z
    } = {3 * Real.pi / 4} := by 
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume r is in the left side, prove equality to 3π/4.
    intro hr
    rcases hr with ⟨x, y, z, hx1, hx2, hy1, hy2, hz1, hz2, h1, h2, h3, hr⟩
    have eq1 : x = Real.pi / 2 - y := by
      have h4 : Real.sin x = Real.cos y := h1
      have h4' : Real.sin x = Real.sin (Real.pi / 2 - y) := by
        have h7 : Real.sin x = Real.cos y := h1
        have h8 : Real.sin (Real.pi / 2 - y) = Real.cos y := by 
          rw [Real.sin_pi_div_two_sub]
        linarith [h7, h8]
      have hx4 : x ≥ 0 := by linarith [hx1]
      have hx5 : x ≤ Real.pi / 2 := by linarith [hx2]
      have h10 : Real.pi / 2 - y ≥ 0 := by
        linarith [Real.pi_pos, hy2]
      have h11 : Real.pi / 2 - y ≤ Real.pi / 2 := by
        linarith [Real.pi_pos, hy1]
      by_cases h13 : x < Real.pi / 2 - y
      · -- Assume x < π/2 - y
        have : Real.sin x < Real.sin (Real.pi / 2 - y) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [hx4, h13, h10, Real.pi_pos]
        linarith
      by_cases h14 : x > Real.pi / 2 - y
      · -- Assume x > π/2 - y
        have : Real.sin x > Real.sin (Real.pi / 2 - y) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [hx4, h14, h11, Real.pi_pos]
        linarith
      linarith
    have eq2 : y = Real.pi / 2 - z := by
      have h5 : Real.sin y = Real.cos z := h2
      have h5' : Real.sin y = Real.sin (Real.pi / 2 - z) := by
        have h5 : Real.sin y = Real.cos z := h2
        have h8 : Real.sin (Real.pi / 2 - z) = Real.cos z := by 
          rw [Real.sin_pi_div_two_sub]
        linarith [h5, h8]
      have h9 : y ≥ 0 := by linarith [hy1]
      have h10 : y ≤ Real.pi / 2 := by linarith [hy2]
      have h11 : Real.pi / 2 - z ≥ 0 := by
        linarith [Real.pi_pos, hz2]
      have h12 : Real.pi / 2 - z ≤ Real.pi / 2 := by
        linarith [Real.pi_pos, hz1]
      by_cases h14 : y < Real.pi / 2 - z
      · -- Assume y < π/2 - z
        have : Real.sin y < Real.sin (Real.pi / 2 - z) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [h9, h14, h11, Real.pi_pos]
        linarith
      by_cases h15 : y > Real.pi / 2 - z
      · -- Assume y > π/2 - z
        have : Real.sin y > Real.sin (Real.pi / 2 - z) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [h9, h15, h12, Real.pi_pos]
        linarith
      linarith
    have eq3 : z = Real.pi / 2 - x := by
      have h3 : Real.sin z = Real.cos x := h3
      have h3' : Real.sin z = Real.sin (Real.pi / 2 - x) := by
        have h3 : Real.sin z = Real.cos x := h3
        have h8 : Real.sin (Real.pi / 2 - x) = Real.cos x := by 
          rw [Real.sin_pi_div_two_sub]
        linarith [h3, h8]
      have h9 : z ≥ 0 := by linarith [hz1]
      have h10 : z ≤ Real.pi / 2 := by linarith [hz2]
      have h11 : Real.pi / 2 - x ≥ 0 := by
        linarith [Real.pi_pos, hx2]
      have h12 : Real.pi / 2 - x ≤ Real.pi / 2 := by
        linarith [Real.pi_pos, hx1]
      by_cases h14 : z < Real.pi / 2 - x
      · -- Assume z < π/2 - x
        have : Real.sin z < Real.sin (Real.pi / 2 - x) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [h9, h14, h11, Real.pi_pos]
        linarith
      by_cases h15 : z > Real.pi / 2 - x
      · -- Assume z > π/2 - x
        have : Real.sin z > Real.sin (Real.pi / 2 - x) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [h9, h15, h12, Real.pi_pos]
        linarith
      linarith
    have eq4 : x + y + z = 3 * Real.pi / 4 := by
      linarith [eq1, eq2, eq3]
    linarith [hr, eq4]
  · -- Show that 3 * π/4 can be achieved.
    intro hr
    rw [hr]
    use Real.pi / 4, Real.pi / 4, Real.pi / 4
    constructor
    · -- Show 0 ≤ x
      linarith [Real.pi_pos]
    constructor
    · -- Show x ≤ π/2
      linarith [Real.pi_pos]
    constructor
    · -- Show 0 ≤ y
      linarith [Real.pi_pos]
    constructor
    · -- Show y ≤ π/2
      linarith [Real.pi_pos]
    constructor
    · -- Show 0 ≤ z
      linarith [Real.pi_pos]
    constructor
    · -- Show z ≤ π/2
      linarith [Real.pi_pos]
    constructor
    · -- Show sin x = cos y
      have h10 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
        have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h7 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith [h6, h7]
      linarith [h10]
    constructor
    · -- Show sin y = cos z
      have h10 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
        have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h7 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith [h6, h7]
      linarith [h10]
    constructor
    · -- Show sin z = cos x
      have h10 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
        have h6 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h7 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        linarith [h6, h7]
      linarith [h10]
    · -- Show r = x + y + z
      linarith [Real.pi_pos]