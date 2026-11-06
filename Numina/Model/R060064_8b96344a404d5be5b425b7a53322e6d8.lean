import Mathlib

/- The perimeter of $\triangle ABC$ is $19$, the lengths of the sides are $a$, $b$, and $c$, and they satisfy $a=b-1$, $c=b+2$, then $a=$ ___          ___ , $b=$ ___          ___ , $c=$ ___          ___. -/
theorem algebra_2603 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) (h4 : a + b + c = 19)
    (h5 : a = b - 1) (h6 : c = b + 2) :
    a = 5 ∧ b = 6 ∧ c = 8 := by
  have eq1 : b = 6 := by
    linarith [h4, h5, h6]
  have eq2 : a = 5 := by
    rw [eq1] at h5
    linarith
  have eq3 : c = 8 := by
    rw [eq1] at h6
    linarith
  constructor
  · exact eq2
  constructor
  · exact eq1
  · exact eq3