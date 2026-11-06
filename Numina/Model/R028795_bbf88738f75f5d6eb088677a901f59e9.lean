import Mathlib

theorem algebra_8150 {x y z : ℝ} (h : x/2 = y/3) (h' : y/3 = z/4) (h'' : z/4 ≠ 0) :
    (4*x - 3*y + 2*z) / (2*x + 3*y - 3*z) = 7 := by
  have h1 : 3 * x = 2 * y := by
    linarith [h]

  have h2 : 4 * y = 3 * z := by
    linarith [h']

  have h3 : y = 3 / 2 * x := by
    linarith

  have h4 : z = 2 * x := by
    rw [h3] at h2
    linarith

  have h5 : x ≠ 0 := by
    by_contra hx
    have h6 : x = 0 := by linarith
    have h7 : z = 0 := by
      rw [h4]
      linarith [h6]

    have h8 : z / 4 = 0 := by
      rw [h7]
      norm_num

    contradiction

  have h6 : 4 * x - 3 * y + 2 * z = 7 * x / 2 := by 
    rw [show y = 3 / 2 * x by linarith [h3], show z = 2 * x by linarith [h4]]
    linarith

  have h7 : 2 * x + 3 * y - 3 * z = x / 2 := by 
    rw [show y = 3 / 2 * x by linarith [h3], show z = 2 * x by linarith [h4]]
    linarith

  have h8 : 2 * x + 3 * y - 3 * z ≠ 0 := by
    intro h9
    have h9' : x / 2 = 0 := by
      have : 2 * x + 3 * y - 3 * z = x / 2 := by linarith [h7]
      linarith [h9, this]
    have h9'' : x = 0 := by 
      linarith
    contradiction

  have h9 : (4 * x - 3 * y + 2 * z) / (2 * x + 3 * y - 3 * z) = 7 := by
    rw [show 4 * x - 3 * y + 2 * z = 7 * x / 2 by linarith [h6], show 2 * x + 3 * y - 3 * z = x / 2 by linarith [h7]]
    have h10 : x / 2 ≠ 0 := by 
      by_contra h2'
      have h3' : x = 0 := by linarith
      contradiction

    field_simp [h10]
    <;> ring

  exact h9