import Mathlib

theorem algebra_163624 (α : ℝ) :
    Real.cos (2 * α) - Real.sin (4 * α) - Real.cos (6 * α) =
    4 * Real.sin (4 * α) * Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12) := by

  have h1 : Real.cos (6 * α) = Real.cos (4 * α) * Real.cos (2 * α) - Real.sin (4 * α) * Real.sin (2 * α) := by
    have h2 : 6 * α = 4 * α + 2 * α := by ring 
    rw [h2] 
    rw [Real.cos_add] 
    <;> ring_nf <;> simp [Real.cos_sq, Real.sin_sq] 
    <;> ring_nf 
  -- The difference expression. We first transform the left side to a desired simpler form before equal to RHS
  have eq2 : Real.cos (2 * α) - Real.sin (4 * α) - Real.cos (6 * α) = 
      2 * Real.sin (4 * α) * (Real.sin (2 * α) - 1 / 2) := by 
    rw [h1]
    have h3 : Real.sin (4 * α) = 2 * Real.sin (2 * α) * Real.cos (2 * α) := by 
      have h4 : 4 * α = 2 * (2 * α) := by ring 
      rw [h4] 
      rw [Real.sin_two_mul]
      <;> ring_nf
    have h4 : Real.cos (4 * α) = 1 - 2 * Real.sin (2 * α) ^ 2 := by 
      have h5 : 4 * α = 2 * (2 * α) := by ring 
      rw [h5] 
      rw [Real.cos_two_mul]
      rw [Real.sin_sq]
      <;> ring_nf 
      <;> simp [Real.cos_sq, Real.sin_sq]
      <;> ring_nf 
    rw [h3] 
    rw [h4] 
    ring_nf 
    <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring_nf 
  -- Transform the right side to the same form as eq2
  -- The right side product multiply. We will use identities here.
  have eq3 : 4 * Real.sin (4 * α) * Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12) = 
      2 * Real.sin (4 * α) * (Real.sin (2 * α) - 1 / 2) := by
    have eq4 : Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12) = (Real.sin (2 * α) - 1 / 2) / 2 := by
      have eq5 : Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12) = (Real.sin (2 * α) - Real.sin (2 * (Real.pi / 12))) / 2 := by
        have h3 : Real.sin (α - Real.pi / 12) = Real.sin α * Real.cos (Real.pi / 12) - Real.cos α * Real.sin (Real.pi / 12) := by 
          rw [Real.sin_sub]
        have h4 : Real.cos (α + Real.pi / 12) = Real.cos α * Real.cos (Real.pi / 12) - Real.sin α * Real.sin (Real.pi / 12) := by 
          rw [Real.cos_add]
        rw [h3, h4]
        have hsin : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
          rw [show 2 * α = 2 * α by ring]
          rw [Real.sin_two_mul]
          <;> ring_nf
        have hsin2 : Real.sin (2 * (Real.pi / 12)) = 2 * Real.sin (Real.pi / 12) * Real.cos (Real.pi / 12) := by 
          rw [show 2 * (Real.pi / 12) = 2 * (Real.pi / 12) by ring]
          rw [Real.sin_two_mul]
          <;> ring_nf
        rw [hsin, hsin2]
        ring_nf 
        <;> simp [Real.sin_sq, Real.cos_sq, Real.sin_sq_add_cos_sq]
        <;> ring_nf <;> simp
      have h6 : Real.sin (2 * (Real.pi / 12)) = 1 / 2 := by 
        have h7 : 2 * (Real.pi / 12) = Real.pi / 6 := by ring_nf 
        rw [h7]
        exact Real.sin_pi_div_six
      rw [eq5]
      rw [h6]
      <;> ring_nf <;> simp 
    have eq5 : 4 * Real.sin (4 * α) * Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12) = 
        4 * Real.sin (4 * α) * (Real.sin (α - Real.pi / 12) * Real.cos (α + Real.pi / 12)) := by ring 
    rw [eq5]
    rw [eq4]
    all_goals ring_nf 
  -- Putting both equations together. The goal is proven.
  rw [eq2]
  rw [eq3]
  all_goals ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq, Real.sin_sq_add_cos_sq]
  <;> ring_nf