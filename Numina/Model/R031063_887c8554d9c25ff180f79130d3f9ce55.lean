import Mathlib

theorem algebra_5419 {m : ℝ} (h : m ≠ 0) (α β : ℝ)
    (h₁ : m * α ^ 2 + (2 * m + 1) * α + m - 3 = 0) (h₂ : m * β ^ 2 + (2 * m + 1) * β + m - 3 = 0) :
    (α - 3) / (α + 1) ^ 2 = (β - 3) / (β + 1) ^ 2 := by

  have h3 : α ≠ -1 := by
    by_contra h3
    rw [show α = -1 by linarith] at h₁
    nlinarith

  have h4 : β ≠ -1 := by
    by_contra h4
    rw [show β = -1 by linarith] at h₂
    nlinarith

  have eq1 : m * (α + 1) ^ 2 = 3 - α := by
    nlinarith

  have eq2 : m * (β + 1) ^ 2 = 3 - β := by
    nlinarith

  have eq3 : (3 - α) * (β + 1) ^ 2 = (3 - β) * (α + 1) ^ 2 := by
    have eq4 : m * (α + 1) ^ 2 = 3 - α := eq1
    have eq5 : m * (β + 1) ^ 2 = 3 - β := eq2
    have eq6 : ( (3 - α) * (β + 1) ^ 2 ) = ( (3 - β) * (α + 1) ^ 2 ) := by
      have eq7 : m ≠ 0 := h
      have eq8 : (3 - α) = m * (α + 1) ^ 2 := by linarith
      have eq13 : (3 - β) = m * (β + 1) ^ 2 := by linarith
      rw [eq8, eq13]
      have eq14 : m * (α + 1) ^ 2 * (β + 1) ^ 2 = m * (β + 1) ^ 2 * (α + 1) ^ 2 := by ring
      have eq15 : m * ( (α + 1) ^ 2 * (β + 1) ^ 2 ) = m * ( (β + 1) ^ 2 * (α + 1) ^ 2 ) := by
        ring_nf
      -- if m≠0 we can cancel from both sides
      have eq16 : (α + 1) ^ 2 * (β + 1) ^ 2 = (β + 1) ^ 2 * (α + 1) ^ 2 := by
        apply (mul_left_inj' h).mp
        linarith
      nlinarith
    linarith

  have h5 : (α - 3) * (β + 1) ^ 2 = (β - 3) * (α + 1) ^ 2 := by
    nlinarith [eq3]

  have h5' : (α + 1) ^ 2 ≠ 0 := by
    have hne1 : α + 1 ≠ 0 := by
      intro h'
      apply h3
      linarith
    intro h'
    have : α + 1 = 0 := by
      apply pow_eq_zero 
      exact h'
    contradiction

  have h5'' : (β + 1) ^ 2 ≠ 0 := by
    have hne2 : β + 1 ≠ 0 := by
      intro h'
      apply h4
      linarith
    intro h'
    have : β + 1 = 0 := by
      apply pow_eq_zero 
      exact h'
    contradiction

  have h5_eq : (α - 3) / (α + 1) ^ 2 = (β - 3) / (β + 1) ^ 2 := by
    field_simp [h5', h5'']
    <;> nlinarith [h5]

  exact h5_eq