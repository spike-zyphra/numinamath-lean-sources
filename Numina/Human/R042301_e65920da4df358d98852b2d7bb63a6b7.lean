import Mathlib

/- 4. Find all values of the parameter $a$, for each of which the equation $a|2+x|+\frac{x^{2}+x-12}{x+4}=0$ has exactly one solution -/
theorem algebra_144828 (a : ℝ) :
    (∃! x, x + 4 ≠ 0 ∧ a * |2 + x| + (x ^ 2 + x - 12) / (x + 4) = 0) ↔
    a ∈ Set.Ioc (-1) 1 ∪ {7 / 2} := by
  -- first convert the division to one linear term using x + 4 ≠ 0
  have (x : ℝ) : x + 4 ≠ 0 ∧ a * |2 + x| + (x ^ 2 + x - 12) / (x + 4) = 0 ↔ x + 4 ≠ 0 ∧ a * |2 + x| + x - 3 = 0 := by
    simp
    rintro h
    rw [show x^2 + x - 12 = (x - 3) * (x + 4) by ring]
    field_simp
    ring_nf
  simp_rw [this]
  constructor
  -- to prove → direction, we contrapose, that is a not in (-1, 1] and a ≠ 7/2, then prove no unique solution
  . contrapose
    rintro ha
    simp at ha
    by_contra h
    -- extract z from unique expression
    obtain ⟨z, ⟨hz1, hz2⟩, hz'⟩ := h
    by_cases h : a ≤ -1
    -- if a ≤ -1, we'll show there is no solution
    . obtain h' | h' := LinearOrder.le_total (2 + z) 0
      -- if 2 + z ≤ 0, then a * |2 + z| + z - 3 = 0 is not possible as a negative, z - 3 also negative
      . rw [abs_eq_neg_self.mpr h'] at hz2
        have : z - 3 < 0 := by linarith
        have : a * -(2 + z) ≤ 0 := by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith
        linarith
      -- if 2 + z ≥ 0 then (a + 1) * (2 + z) ≤ 0 implies the expression is not possible
      . rw [abs_eq_self.mpr h'] at hz2
        have : (a + 1) * (2 + z) ≤ 0 := by apply mul_nonpos_of_nonpos_of_nonneg <;> linarith
        linarith
    -- other wise a ≠ 7/2 and a > 1
    . simp at h
      simp [h] at ha
      have : 0 < 1 + a := by linarith
      have : 1 - a ≠ 0 := by linarith
      -- we'll show x and y as defined below are two solutinos
      let x := (3 - a * 2) / (1 + a)
      let y := (3 + a * 2) / (1 - a)
      -- pluggin in x, we see both requirements are proved (0 ≤ 2 + x)
      have hx : x + 4 ≠ 0 ∧ a * |2 + x| + x - 3 = 0 := by
        and_intros
        . simp [x]
          field_simp
          by_contra h
          replace h : a = -7 / 3 := by linarith
          rw [h] at ha
          have ha := ha.right
          norm_num at ha
        . have : 0 ≤ 2 + x := by simp [x]; field_simp; ring_nf; positivity
          rw [abs_eq_self.mpr this]
          simp [x]
          field_simp
          ring
      -- pluggin in y,, we see both requirements are proved (2 + y ≤ 0)
      have hy : y + 4 ≠ 0 ∧ a * |2 + y| + y - 3 = 0 := by
        and_intros
        . simp [y]
          field_simp
          by_contra h
          replace h : a = 7 / 2 := by linarith
          exact ha.left h
        . have : 1 - a < 0 := by linarith
          have : 2 + y ≤ 0 := by
            simp [y]
            field_simp
            ring_nf
            apply mul_nonpos_of_nonpos_of_nonneg
            . exact le_of_lt (inv_lt_zero.mpr this)
            . norm_num
          rw [abs_eq_neg_self.mpr this]
          simp [y]
          field_simp
          ring
      -- next x ≠ y, also proved by manipulation (as a ≠ 0)
      replace hx := hz' x hx
      replace hy := hz' y hy
      have : x ≠ y := by
        by_contra h
        simp [x, y] at h
        field_simp at h
        ring_nf at h
        have : a = 0 := by linarith
        rw [this] at ha
        have ha := ha.right
        simp at ha
        norm_num at ha
      -- this proves unique solution not possible
      rw [hx, hy] at this
      simp at this
  -- now the ← direction
  . simp; rintro h
    -- if a = 7/2 then -8/9 is unique solution
    obtain rfl | ha := h
    . use -8/9
      norm_num
      simp [abs_div]
      and_intros
      . norm_num
      . rintro y hy hy'
        -- to prove uniqueness casework on 2 + y and 0's relative order, first case not possible
        obtain h | h := LinearOrder.le_total (2 + y) 0
        . rw [abs_eq_neg_self.mpr h] at hy'
          have : y + 4 = 0 := by linarith
          contradiction
        . rw [abs_eq_self.mpr h] at hy'
          linarith
    -- otherwise (3 - 2a)/(a+1) is unique solution
    . use (3 - 2 * a) / (a + 1)
      have : 0 < a + 1 := by linarith
      field_simp
      ring_nf
      and_intros
      . linarith
      . ring_nf at this
        have : 0 ≤ (1 + a)⁻¹ * 5 := by positivity
        rw [abs_eq_self.mpr this]
        field_simp
        ring
      -- to prove uniqueness, casework on relative order of 2+y, 0
      . rintro y hy hy'
        obtain h | h := LinearOrder.le_total (2 + y) 0
        . rw [abs_eq_neg_self.mpr h] at hy'
          by_cases ha' : a = 1
          . rw [ha'] at hy'
            ring_nf at hy'
            norm_num at hy'
          . replace hy' : -5 + (2 + y) * (-a + 1) = 0 := by linear_combination hy'
            have : (2 + y) * (-a + 1) ≤ 0 := by
              apply mul_nonpos_of_nonpos_of_nonneg <;> linarith
            linarith
        . rw [abs_eq_self.mpr h] at hy'
          linear_combination hy'