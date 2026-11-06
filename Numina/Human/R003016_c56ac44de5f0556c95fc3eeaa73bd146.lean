import Mathlib

/- 4. A body of mass $m$ is attached to one end of a weightless, inextensible string, the other end of which is attached to the ceiling. The string is passed over a pulley of mass $M$, which is concentrated on its axis. At the initial moment, the body is held and then released. Find the accelerations of the body and the pulley.

![](https://cdn.mathpix.com/cropped/2024_05_06_98019744d8c01484e6a0g-1.jpg?height=171&width=1077&top_left_y=1202&top_left_x=158) -/
theorem calculus_143988 {a₁ a₂ g m M T : ℝ} (hm : 0 < m) (hM : 0 < M)
  (h₁ : m * a₁ = m * g + T)
  (h₂ : M * a₂ = M * g - 2 * T)
  (h₃ : a₁ = 2 * a₂) :
  a₁ = 2 * g * (2 * m + M) / (4 * m + M) ∧ a₂ = g * (2 * m + M) / (4 * m + M) := by
  -- substitute equation (3) into equation (1)
  rw [h₃] at h₁ ⊢
  constructor
  all_goals field_simp
  rotate_right
  -- eliminate T from equations (1) and (2) and conclude
  · calc
      a₂ * (4 * m + M) = m * (2 * a₂) * 2 + M * a₂ := by ring
      _ = g * (2 * m + M) := by rw [h₁, h₂]; ring
  · calc
      2 * a₂ * (4 * m + M) = m * (2 * a₂) * 4 + M * a₂ * 2 := by ring
      _ = 2 * g * (2 * m + M) := by rw [h₁, h₂]; ring