import Mathlib

open Real



/--
A structure representing a line in the form \( a x + b y + c = 0 \).
-/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  deriving Inhabited

/--
Defines the condition for two lines \( l1 \) and \( l2 \) to be perpendicular.
Two lines are perpendicular if the dot product of their direction vectors is zero, i.e., \( a_1 a_2 + b_1 b_2 = 0 \).
-/
def perpendicular (l1 l2 : Line) : Prop := l1.a * l2.a + l1.b * l2.b = 0

theorem algebra_9149 {m : ℝ} (l1 l2 : Line)
  (hl1 : l1 = Line.mk 1 (-m) (2*m))
  (hl2 : l2 = Line.mk 1 2 (-m))
  (h : perpendicular l1 l2) : m = 1 / 2 := by 
  rw [perpendicular] at h
  rw [hl1] at h 
  rw [hl2] at h
  simp [Line] at h 
  linarith