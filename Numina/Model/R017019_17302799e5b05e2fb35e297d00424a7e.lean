import Mathlib


theorem algebra_229084 {a b c : ℝ} (h : a * b + b * c + c * a = 3) :
    (a * (b ^ 2 + 3)) / (a + b) + (b * (c ^ 2 + 3)) / (b + c) +
    (c * (a ^ 2 + 3)) / (c + a) = 6 := by


  have h1 : a + b ≠ 0 := by
    by_contra h1
    have ha : a = -b := by linarith
    rw [ha] at h
    nlinarith [sq_nonneg b]

  have h2 : b + c ≠ 0 := by
    by_contra h2
    have hb : b = -c := by linarith
    rw [hb] at h
    nlinarith [sq_nonneg c]

  have h3 : c + a ≠ 0 := by
    by_contra h3
    have hc : c = -a := by linarith
    rw [hc] at h
    nlinarith [sq_nonneg a]

  have eq1 : b ^ 2 + 3 = (a + b) * (b + c) := by
    nlinarith [h]

  have eq2 : c ^ 2 + 3 = (b + c) * (c + a) := by
    nlinarith [h]

  have eq3 : a ^ 2 + 3 = (c + a) * (a + b) := by
    nlinarith [h]

  have eq4 : (a * (b ^ 2 + 3)) / (a + b) = a * (b + c) := by
    rw [eq1]
    field_simp [h1]
    <;> nlinarith

  have eq5 : (b * (c ^ 2 + 3)) / (b + c) = b * (c + a) := by
    rw [eq2]
    field_simp [h2]
    <;> nlinarith

  have eq6 : (c * (a ^ 2 + 3)) / (c + a) = c * (a + b) := by
    rw [eq3]
    field_simp [h3]
    <;> nlinarith

  rw [eq4, eq5, eq6]

  nlinarith [h, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]