import Mathlib

open Real Set
open scoped Real

theorem algebra_185681 (α β : ℝ) :
  (cos α - cos (2 * β))^2 + (sin α + sin (2 * β))^2 =
  4 * (sin ((α + 2 * β) / 2))^2 := by
  have h1 : (cos α - cos (2 * β)) ^ 2 + (sin α + sin (2 * β)) ^ 2 =
      (cos α) ^ 2 - 2 * (cos α) * (cos (2 * β)) + (cos (2 * β)) ^ 2 + (sin α) ^ 2 + 2 * (sin α) * (sin (2 * β)) + (sin (2 * β)) ^ 2 := by
    ring
  rw [h1]
  have h2 : (cos α) ^ 2 + (sin α) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq α
  have h3 : (cos (2 * β)) ^ 2 + (sin (2 * β)) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (2 * β)
  have eq1 : (cos α) ^ 2 - 2 * (cos α) * (cos (2 * β)) + (cos (2 * β)) ^ 2 + (sin α) ^ 2 + 2 * (sin α) * (sin (2 * β)) + (sin (2 * β)) ^ 2 =
      2 + 2 * (sin α * sin (2 * β) - cos α * cos (2 * β)) := by
    calc
      (cos α) ^ 2 - 2 * (cos α) * (cos (2 * β)) + (cos (2 * β)) ^ 2 + (sin α) ^ 2 + 2 * (sin α) * (sin (2 * β)) + (sin (2 * β)) ^ 2
        = ((cos α) ^ 2 + (sin α) ^ 2) + ((cos (2 * β)) ^ 2 + (sin (2 * β)) ^ 2) + 2 * (sin α * sin (2 * β) - cos α * cos (2 * β)) := by
          ring_nf
      _ = 1 + 1 + 2 * (sin α * sin (2 * β) - cos α * cos (2 * β)) := by
        rw [h2, h3]
      _ = 2 + 2 * (sin α * sin (2 * β) - cos α * cos (2 * β)) := by
        ring_nf
  rw [eq1]
  have h8 : sin α * sin (2 * β) - cos α * cos (2 * β) = - (cos (α + 2 * β)) := by
    have h9 : cos (α + 2 * β) = cos α * cos (2 * β) - sin α * sin (2 * β) := by
      rw [cos_add]
      <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
      <;> linarith
    rw [h9]
    ring_nf
    <;> simp [Real.sin_sq, Real.cos_sq]
    <;> linarith
  rw [h8]
  have h10 : 1 - cos (α + 2 * β) = 2 * (sin ((α + 2 * β) / 2)) ^ 2 := by
    have h11 : (sin ((α + 2 * β) / 2)) ^ 2 = (1 - cos (α + 2 * β)) / 2 := by
      have h12 : (sin ((α + 2 * β) / 2)) ^ 2 = (1 - cos (α + 2 * β)) / 2 := by
        rw [Real.sin_sq_eq_half_sub]
        <;> ring_nf <;> linarith
      linarith
    linarith
  have eq2 : 2 + 2 * (- (cos (α + 2 * β))) = 4 * (sin ((α + 2 * β) / 2)) ^ 2 := by
    calc
      2 + 2 * (- (cos (α + 2 * β))) = 2 * (1 - cos (α + 2 * β)) := by ring_nf
      _ = 2 * (2 * (sin ((α + 2 * β) / 2)) ^ 2) := by 
        rw [h10]
        all_goals linarith
      _ = 4 * (sin ((α + 2 * β) / 2)) ^ 2 := by ring_nf
  linarith [eq2]