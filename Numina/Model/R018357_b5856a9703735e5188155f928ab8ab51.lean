import Mathlib

theorem algebra_276414 {x : ℝ} (hx : x ≠ 0) (α : ℝ) (h : x + 1 / x = 2 * Real.cos α) (n : ℕ) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by

  have h1 : ∀ (n : ℕ), x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by 
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      have eq1 : x ^ 0 + 1 / x ^ 0 = (2 : ℝ) := by
        field_simp
        <;> norm_num 
      have eq2 : 2 * Real.cos (0 * α) = (2 : ℝ) := by
        have h : Real.cos (0 * α) = 1 := by 
          have h11 : 0 * α = (0 : ℝ) := by ring
          rw [h11]
          exact Real.cos_zero
        rw [h]
        all_goals linarith
      linarith [eq1, eq2]
    | succ n =>
      cases n with
      | zero =>
        have eq3 : x ^ 1 + 1 / x ^ 1 = 2 * Real.cos (1 * α) := by
          have eq4 : x ^ 1 + 1 / x ^ 1 = x + 1 / x := by
            ring_nf
          rw [eq4]
          have eq5 : x + 1 / x = 2 * Real.cos α := h
          have eq6 : (1 * α) = α := by ring
          rw [eq6]
          linarith [eq5]
        simpa using eq3 
      | succ k =>
        have h7 := ih (k) (by omega)
        have h8 := ih (k+1) (by omega)
        have eq1 : x ^ (k + 2) + 1 / x ^ (k + 2) = (x ^ (k + 1) + 1 / x ^ (k + 1)) * (x + 1 / x) - (x ^ k + 1 / x ^ k) := by 
          field_simp 
          <;> ring
        rw [eq1]
        rw [h8]
        rw [h7]
        have h2 : x + 1 / x = 2 * Real.cos α := h
        rw [h2]
        have h4 : 2 * Real.cos (↑(k + 1) * α) * (2 * Real.cos α) - 2 * Real.cos (↑k * α) = 2 * Real.cos (↑(k + 2) * α) := by 
          have h5 : Real.cos (↑(k + 2) * α) = Real.cos (↑(k + 1) * α + α) := by 
            have h6 : ↑(k + 2) * α = (↑(k + 1) * α + α) := by 
              simp at *
              <;> ring_nf 
            rw [h6]
          have h6 : Real.cos (↑(k + 1) * α + α) = Real.cos (↑(k + 1) * α) * Real.cos α - Real.sin (↑(k + 1) * α) * Real.sin α := by 
            rw [Real.cos_add]
          rw [h5, h6]
          have h7 : Real.cos (↑k * α) = Real.cos (↑(k + 1) * α - α) := by 
            have h8 : ↑k * α = (↑(k + 1) * α - α) := by 
              simp at *
              <;> ring_nf
            rw [h8]
          have h8 : Real.cos (↑(k + 1) * α - α) = Real.cos (↑(k + 1) * α) * Real.cos α + Real.sin (↑(k + 1) * α) * Real.sin α := by 
            rw [Real.cos_sub]
          rw [h7, h8]
          ring
        linarith [h4]
  specialize h1 n
  simpa using h1