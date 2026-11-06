import Mathlib

/-Real numbers a, b and c are different from zero and satisfy the equations
a^a+a=b^2,b^2+b=c^2,c^2+c=a^2, prove that (a-b)(b-c)(c-a)=1-/
theorem algebra_216783 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + a = b^2) (h2 : b^2 + b = c^2) (h3 : c^2 + c = a^2) :
    (a - b) * (b - c) * (c - a) = 1 := by

-- we prove the result step by step --
  have h4 : a + b + c = 0 := by
    nlinarith

  have eq1 : a^2 - b^2 = -a := by linarith
  have eq2 : b^2 - c^2 = -b := by linarith
  have eq3 : c^2 - a^2 = -c := by linarith

-- from eq1, eq2 and eq3 we write (a^2 - b^2)(b^2 - c^2)(c^2 - a^2) in two ways --
  have h5 : (a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2) = (-a) * (-b) * (-c) := by
    rw [eq1, eq2, eq3]

  have h6 : (a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2) = (a - b) * (a + b) * (b - c) * (b + c) * (c - a) * (c + a) := by
    ring

  rw [h6] at h5

  have h7 : (a + b) = -c := by linarith [h4]
  have h8 : (b + c) = -a := by linarith [h4]
  have h9 : (c + a) = -b := by linarith [h4]

  rw [h7, h8, h9] at h5
-- from this, we get what we want, the rest is a simple modify --
  have h10 : (a - b) * (b - c) * (c - a) * (-a * b * c) = -a * b * c := by
    nlinarith

  have h11 : (a - b) * (b - c) * (c - a) = 1 := by
    have h12 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      · exact ha
      · exact hb
      · exact hc

    have h13 : (a - b) * (b - c) * (c - a) = 1 := by
      apply (mul_left_inj' h12).mp
      linarith

    exact h13

  exact h11