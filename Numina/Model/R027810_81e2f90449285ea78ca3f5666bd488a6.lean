import Mathlib

open Real Set
open scoped Real

theorem algebra_186041 (α : Real) :
  -cos (5 * α) * cos (4 * α) - cos (4 * α) * cos (3 * α) +
  2 * (cos (2 * α))^2 * cos α = 2 * cos α * sin (2 * α) * sin (6 * α) := by
  have h1 : cos (5 * α) * cos (4 * α) = (1 / 2) * (cos (9 * α) + cos (α)) := by 
    have h1 : cos (5 * α) * cos (4 * α) = (1 / 2) * (cos (9 * α) + cos (α)) := by
      have h2 : cos (5 * α) * cos (4 * α) = (1 / 2) * (cos (5 * α + 4 * α) + cos (5 * α - 4 * α)) := by 
        rw [cos_add, cos_sub]
        ring_nf
      have h3 : 5 * α + 4 * α = 9 * α := by ring
      have h4 : 5 * α - 4 * α = α := by ring
      rw [h3, h4] at h2
      linarith
    linarith
  have h2 : cos (4 * α) * cos (3 * α) = (1 / 2) * (cos (7 * α) + cos (α)) := by
    have h2 : cos (4 * α) * cos (3 * α) = (1 / 2) * (cos (7 * α) + cos (α)) := by 
      have h3 : cos (4 * α) * cos (3 * α) = (1 / 2) * (cos (4 * α + 3 * α) + cos (4 * α - 3 * α)) := by 
        rw [cos_add, cos_sub]
        ring_nf 
      have h4 : 4 * α + 3 * α = 7 * α := by ring 
      have h5 : 4 * α - 3 * α = α := by ring 
      rw [h4, h5] at h3 
      linarith 
    linarith 
  have h3 : 2 * (cos (2 * α))^2 = 1 + cos (4 * α) := by 
    have h4 : 2 * (cos (2 * α))^2 = 1 + cos (4 * α) := by 
      have h5 : cos (4 * α) = 2 * (cos (2 * α))^2 - 1 := by 
        rw [show 4 * α = 2 * (2 * α) by ring]
        exact cos_two_mul (2 * α)
      linarith 
    linarith 
  have eq4 : -cos (5 * α) * cos (4 * α) - cos (4 * α) * cos (3 * α) + 2 * (cos (2 * α))^2 * cos α =
      - (1 / 2) * cos (9 * α) - (1 / 2) * cos (7 * α) + cos (4 * α) * cos α := by 
    calc
      -cos (5 * α) * cos (4 * α) - cos (4 * α) * cos (3 * α) + 2 * (cos (2 * α))^2 * cos α
          = - (cos (5 * α) * cos (4 * α)) - (cos (4 * α) * cos (3 * α)) + (2 * (cos (2 * α))^2) * cos α := by ring
      _ = - ( (1 / 2) * (cos (9 * α) + cos α) ) - ( (1 / 2) * (cos (7 * α) + cos α) ) + (2 * (cos (2 * α))^2) * cos α := by 
        rw [h1, h2] 
      _ = - (1 / 2) * cos (9 * α) - (1 / 2) * cos (7 * α) + cos (4 * α) * cos α := by
        rw [h3]
        all_goals ring 
  rw [eq4]
  have h5 : - (1 / 2) * cos (9 * α) - (1 / 2) * cos (7 * α) + cos (4 * α) * cos α = 
      cos (4 * α) * cos α - (1 / 2) * (cos (9 * α) + cos (7 * α)) := by ring
  rw [h5]
  have h7 : cos (9 * α) + cos (7 * α) = 2 * cos (8 * α) * cos (α) := by 
    have h7 : cos (9 * α) + cos (7 * α) = 2 * cos (8 * α) * cos (α) := by 
      rw [show 9 * α = 8 * α + α by ring, 
          show 7 * α = 8 * α - α by ring]
      rw [cos_add, cos_sub]
      ring_nf 
    linarith
  have h5' : cos (4 * α) * cos α - (1 / 2) * (cos (9 * α) + cos (7 * α)) = 
      cos α * (cos (4 * α) - cos (8 * α)) := by 
    rw [show cos (9 * α) + cos (7 * α) = 2 * cos (8 * α) * cos (α) by linarith [h7]]
    linarith 
  rw [h5']
  have h6 : cos α * (cos (4 * α) - cos (8 * α)) = 2 * cos α * sin (2 * α) * sin (6 * α) := by
    have h7 : cos (4 * α) - cos (8 * α) = 2 * sin (6 * α) * sin (2 * α) := by
      have h8 : cos (4 * α) - cos (8 * α) = -2 * sin ((4 * α + 8 * α) / 2) * sin ((4 * α - 8 * α) / 2) := by 
        rw [cos_sub_cos]
      have h9 : (4 * α + 8 * α) / 2 = 6 * α := by ring_nf 
      have h10 : (4 * α - 8 * α) / 2 = - (2 * α) := by ring_nf 
      rw [h9, h10] at h8 
      have h11 : -2 * sin (6 * α) * sin (- (2 * α)) = 2 * sin (6 * α) * sin (2 * α) := by 
        simp [sin_neg]
        <;> ring_nf 
      linarith 
    have h8 : cos α * (cos (4 * α) - cos (8 * α)) = cos α * (2 * sin (6 * α) * sin (2 * α)) := by
      rw [h7]
    linarith [h8]
  exact h6