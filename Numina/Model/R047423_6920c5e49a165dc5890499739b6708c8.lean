import Mathlib
theorem algebra_308562 (x y z k : ℝ)
  (hx : x / (y + z) = k)(hyz : y + z ≠ 0)
  (hy : y / (z + x) = k)(hzx : z + x ≠ 0)
  (hz : z / (x + y) = k)(hxy : x + y ≠ 0) :
  (x + y + z ≠ 0 → k = 1 / 2) ∧ (x + y + z = 0 → k = -1) := by
  constructor
  · -- Assume x + y + z ≠ 0, need to prove k = 1 / 2
    intro h1
    have eq1 : x = k * (y + z) := by
      have h1' : y + z ≠ 0 := hyz
      field_simp [h1'] at hx
      linarith
    have eq2 : y = k * (z + x) := by
      have h2' : z + x ≠ 0 := hzx
      field_simp [h2'] at hy
      linarith
    have eq3 : z = k * (x + y) := by
      have h3' : x + y ≠ 0 := hxy
      field_simp [h3'] at hz
      linarith
    have eq4 : x + y + z = 2 * k * (x + y + z) := by
      nlinarith
    have hk : k = 1 / 2 := by
      apply (mul_left_inj' h1).mp
      linarith
    exact hk
  · -- Assume x + y + z = 0, need to prove k = -1
    intro h2
    have eq1 : x = k * (y + z) := by
      have h1' : y + z ≠ 0 := hyz
      field_simp [h1'] at hx
      linarith
    have eq2 : y = k * (z + x) := by
      have h2' : z + x ≠ 0 := hzx
      field_simp [h2'] at hy
      linarith
    have eq3 : z = k * (x + y) := by
      have h3' : x + y ≠ 0 := hxy
      field_simp [h3'] at hz
      linarith
    have eq5 : z = - (x + y) := by
      have h : x + y + z = 0 := h2
      linarith
    by_cases h3 : x + y = 0
    · -- Case x + y = 0, so z = 0
      have h4 : z = 0 := by
        nlinarith [eq5, h3]
      have eq1' : x = k * y := by 
        rw [show z = 0 by linarith [h4]] at eq1
        linarith 
      have eq2' : y = k * x := by 
        rw [show z = 0 by linarith [h4]] at eq2 
        linarith 
      by_cases h5 : y = 0 
      · -- Case y = 0, which leads to contradiction
        have h6 : x = 0 := by
          nlinarith [h3, h5]
        have h7 : y + z = 0 := by
          nlinarith [h6, h5, h4]
        exfalso
        exact hyz h7
      · -- Case y ≠ 0 
        have hk : k = -1 := by
          have h8 : x = -y := by nlinarith [h3]
          have eq3'' : x = -y := by nlinarith [h3]
          have eq1'' : x = k * y := by linarith [eq1']
          have eq2'' : y = k * x := by linarith [eq2']
          have eq_a : -y = k * y := by
            have eqx : x = -y := by linarith [h3]
            rw [eqx] at eq1''
            linarith [eq1'']
          have : k = -1 := by
            apply (mul_left_inj' h5).mp
            linarith [eq_a]
          assumption
        exact hk
    · -- Case x + y ≠ 0
      have eq5' : k * (x + y) = - (x + y) := by
        have h7 : z = - (x + y) := eq5
        have eq3' : z = k * (x + y) := eq3
        linarith [h7, eq3']
      have eq7 : k = -1 := by
        apply (mul_left_inj' (show x + y ≠ 0 by exact h3)).mp
        linarith [eq5']
      exact eq7