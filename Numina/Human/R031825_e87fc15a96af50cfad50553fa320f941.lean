import Mathlib

/- Charlie is riding on his unicycle. If the unicycle's wheel has a radius of 9 inches and makes 2 revolutions every 3 seconds, what is the unicycle's speed in inches per second? -/
theorem algebra_20287 (radius : ℝ) (hr : radius = 9) (speed : ℝ) (h : speed * 3 = 2 * (2 * π * radius)) :
    speed = 12 * π := by
  -- $\mathrm{speed} \cdot 3 = 2 \cdot (2 \cdot \pi \cdot \mathrm{radius})$
  rw [hr] at h
  -- $\mathrm{speed} = 2 \cdot (2 \cdot \pi \cdot 9) / 3$
  apply congrArg (fun x ↦ x / 3) at h
  ring_nf at h
  -- $\mathrm{speed} = 12 \cdot \pi$
  rw [h, mul_comm]