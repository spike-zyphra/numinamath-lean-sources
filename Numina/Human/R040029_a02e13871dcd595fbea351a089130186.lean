import Mathlib

/-- A segment with endpoints at $A(2, -2)$ and $B(14, 4)$ is extended through $B$ to point $C$. If $BC = \frac{1}{3} \cdot AB$, what are the coordinates for point $C$? Express your answer as an ordered pair.-/
theorem algebra_4091 {A B C : ℝ × ℝ}
    (hA : A = (2, -2)) (hB : B = (14, 4)) (hC : C - B = 1 / 3 * (B - A)) :
    C = (18, 6) := by
  cases' C with x y
  -- Use `rw` to substitute, calculate the horizontal and vertical coordinates respectively, and use `linarith` to automatically solve the linear equation
  rw [hA, hB] at hC
  have h₁ := congr_arg Prod.fst hC
  have h₂ := congr_arg Prod.snd hC
  simp at h₁ h₂
  norm_num at h₁ h₂
  ext
  · change x = 18; linarith
  · change y = 6; linarith
