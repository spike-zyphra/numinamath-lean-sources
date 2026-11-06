import Mathlib

theorem algebra_213597 {a : ℝ} (ha : a^2/4 - 4/a^2 = 5) :
    (a^12 - 4096)/(64*a^6) = 140 := by
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have ha2 : a^4 / 4 - 4 = 5 * a^2 := by
    have h1 : a^2 ≠ 0 := by
      intro h
      apply ha1
      nlinarith
    have h2 : a^2/4 - 4/a^2 = (a^4 / 4 - 4) / a^2 := by
      field_simp [h1]
      <;> nlinarith
    rw [h2] at ha
    have h3 : (a^4 / 4 - 4) / a^2 = 5 := by linarith
    have h4 : a^4 / 4 - 4 = 5 * a^2 := by 
      field_simp [h1] at h3 ⊢
      <;> nlinarith 
    linarith
  have ha3 : a^4 - 20 * a^2 - 16 = 0 := by
    nlinarith [ha2]
  have ha4 : a^2 ≠ 0 := by
    intro h
    apply ha1
    nlinarith
  have ha5 : a^6 ≠ 0 := by
    have ha1 : a ≠ 0 := ha1
    have h5 : a^6 = a^2 * a^2 * a^2 := by ring
    rw [h5]
    have h4 : a^2 ≠ 0  := by
      intro h
      apply ha1
      nlinarith
    have h3 : a^2 * a^2 * a^2 ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact h4
      exact h4
      exact h4
    simpa using h3
  have h1 : a^12 - 4096 = 140 * (64 * a^6) := by
    have ha6 : a^6 = 416 * a^2 + 320 := by
      have ha7 : a^6 = a^2 * a^4 := by ring
      rw [ha7]
      have ha8 : a^4 = 20 * a^2 + 16 := by
        nlinarith [ha3]
      rw [ha8]
      nlinarith [sq_nonneg (a^2 - 10), sq_nonneg (a^2 + 10)]
    have ha7 : a^12 = (416 * a^2 + 320) ^ 2 := by
      have h6 : a^6 = 416 * a^2 + 320 := ha6
      calc
        a^12 = (a^6) ^ 2 := by ring
        _ = (416 * a^2 + 320) ^ 2 := by rw [h6]
    nlinarith [ha7, sq_nonneg (a^2 - 10), sq_nonneg (a^2 + 10), sq_nonneg (a^4 - 20 * a^2), sq_nonneg (a^4 + 16), sq_nonneg (a^2 - 4), sq_nonneg (a^2 + 4)]
  have h2 : (a^12 - 4096) / (64 * a^6) = 140 := by
    have h3 : a^6 ≠ 0 := ha5
    have h4 : (a^12 - 4096) = 140 * (64 * a^6) := by
      nlinarith [h1]
    have h5 : (a^12 - 4096) / (64 * a^6) = 140 := by
      rw [h4]
      field_simp [show a^6 ≠ 0 by exact h3, show a ≠ 0 by exact ha1]
      <;> nlinarith
    exact h5
  exact h2