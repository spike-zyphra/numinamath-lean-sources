import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

variable (P : ℝ × ℝ)

def lies_on_vertical_parabola (p : ℝ) (point : ℝ × ℝ) : Prop :=
  (point.2)^2 = 2*p*(point.1)

def lies_on_horizontal_parabola (p : ℝ) (point : ℝ × ℝ) : Prop :=
  (point.1)^2 = 2*p*(point.2)

lemma vertical_parabola_param (P : ℝ × ℝ) (h : P = (4, -2)) :
  lies_on_vertical_parabola (1/2) P := by
  rw [lies_on_vertical_parabola, h]
  simp
  ring

lemma horizontal_parabola_param (P : ℝ × ℝ) (h : P = (4, -2)) :
  lies_on_horizontal_parabola (-4) P := by
  rw [lies_on_horizontal_parabola, h]
  simp
  ring

theorem algebra_9255 (P : ℝ × ℝ) (h : P = (4, -2)) :
  (∃ p : ℝ, p > 0 ∧ lies_on_vertical_parabola p P) ∨
  (∃ p : ℝ, p > 0 ∧ lies_on_horizontal_parabola (-p) P) := by
  left
  use 1 / 2
  constructor
  · norm_num
  · -- Check that P lies on a vertical parabola with parameter 1/2
    rw [h]
    simp [lies_on_vertical_parabola]
    all_goals norm_num