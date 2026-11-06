import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

-- Define the point P(4,-2)
variable (P : ℝ × ℝ)

-- Helper function to check if a point lies on a vertical parabola
def lies_on_vertical_parabola (p : ℝ) (point : ℝ × ℝ) : Prop :=
  (point.2)^2 = 2*p*(point.1)

-- Helper function to check if a point lies on a horizontal parabola
def lies_on_horizontal_parabola (p : ℝ) (point : ℝ × ℝ) : Prop :=
  (point.1)^2 = 2*p*(point.2)

-- Lemma for vertical parabola case
lemma vertical_parabola_param (P : ℝ × ℝ) (h : P = (4, -2)) :
  lies_on_vertical_parabola (1/2) P := by
  rw [lies_on_vertical_parabola, h]
  simp
  ring

-- Lemma for horizontal parabola case
lemma horizontal_parabola_param (P : ℝ × ℝ) (h : P = (4, -2)) :
  lies_on_horizontal_parabola (-4) P := by
  rw [lies_on_horizontal_parabola, h]
  simp
  ring

/-Find the standard equation of the parabola that passes through the point $P(4,-2)$.-/
theorem algebra_9255 (P : ℝ × ℝ) (h : P = (4, -2)) :
  (∃ p : ℝ, p > 0 ∧ lies_on_vertical_parabola p P) ∨
  (∃ p : ℝ, p > 0 ∧ lies_on_horizontal_parabola (-p) P) := by
  left
  use 1/2
  constructor
  · norm_num
  · exact vertical_parabola_param P h