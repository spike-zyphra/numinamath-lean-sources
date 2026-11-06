import Mathlib

theorem algebra_19767 {d e : ℝ} (hd : d^2 + (3 / 2) * d - (5 / 2) = 0) (he : e^2 + (3 / 2) * e - (5 / 2) = 0)
    (hde : d ≠ e) : (d - 1) * (e - 1) = 0 := by

  have h1 : 2 * d^2 + 3 * d - 5 = 0 := by 
    nlinarith

  have h2 : 2 * e^2 + 3 * e - 5 = 0 := by
    nlinarith
  
  have h3 : (d - 1) * (d + 5 / 2) = 0 := by
    nlinarith [h1]

  have h4 : (e - 1) * (e + 5 / 2) = 0 := by
    nlinarith [h2]

  cases (mul_eq_zero.mp h3) with
  | inl h5 =>
    simp [h5]
  | inr h6 =>
    have hd' : d = -5 / 2 := by linarith
    have h5 : e = 1 := by
      cases (mul_eq_zero.mp h4) with
      | inl h6 =>
        linarith
      | inr h7 =>
        have he' : e = -5 / 2 := by linarith
        exfalso
        have h_eq : d = e := by
          linarith [hd', he']
        contradiction
    rw [h5]
    simp
    <;> nlinarith