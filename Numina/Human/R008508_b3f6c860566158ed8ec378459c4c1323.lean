import Mathlib

/- On a particular January day, the high temperature in Lincoln, Nebraska, was 1616 degrees higher
than the low temperature, and the average of the high and low temperatures was 33.
In degrees, what was the low temperature in Lincoln that day?
(A) −13 (B) −8 (C) −5 (D) −3 (E) 11 -/
theorem algebra_94502 {h l : ℝ} (hhl : h = l + 16) (havg : (h + l) / 2 = 3) :
l = -5 := by
  -- substitute `h = l + 16` into `(h+l)/2=3`.
  rw [hhl] at havg
  -- obtain `l+16+l = 2*3` from `(l+16+l)/2 = 3`
  have h₁ := congrArg (fun k => k * 2) havg
  simp at h₁
  -- group like terms
  rw [add_comm, ← add_assoc, ← two_mul l] at h₁
  -- bring `16` to the other side of the equation
  have h₂ := (sub_eq_iff_eq_add.mpr h₁.symm).symm
  -- numerical simplification
  have : (3 * 2 - 16 : ℝ) = -10 := by ring
  rw [this] at h₂
  have : l = -10 / 2 := by rw [h₂.symm]; simp
  have done : (-10 / 2 : ℝ) = -5 := by norm_num
  rw [done] at this
  assumption