import Mathlib

open Real 

theorem Algebra_608393 {t : ℝ} (h : (100 * t - (1/2) * t^2 = 1875 + (1/2) * t^2)): 
  t = 25 ∨ t = 75 := by
  ring_nf at h
  have heq : 1875 + t ^ 2 * (1 / 2) - t * 100 - t ^ 2 * (- 1/ 2) = 0:= by 
    rw [←h]
    ring_nf
-- solve this equation 1875 - t*100+t^2=0 we get t=25 or t=75.
  have heq' :(t - 25) * (t - 75) =  0 := by 
    calc 
      _ = 1875 + t ^ 2 * (1 / 2) - t * 100 - t ^ 2 * (- 1/ 2) := by ring
      _ = 0 := heq
  obtain h' := mul_eq_zero.mp heq'
  obtain h₁ | h₂ := h'
  -- the only posible case is that t =25 
  left
  · rw [←add_zero 25, ←h₁]
    ring
  right
  rw [←add_zero 75, ←h₂]
  ring