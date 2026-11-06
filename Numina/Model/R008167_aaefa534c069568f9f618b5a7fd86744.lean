import Mathlib

theorem algebra_98593 {P Q : ℝ → ℝ} {b c d e : ℝ} (hP : P = fun x => 2 * x^2 + b * x + c)
    (hQ : Q = fun x => -2 * x^2 + d * x + e) (hP1 : P 16 = 54) (hP2 : P 20 = 53)
    (hQ1 : Q 16 = 54) (hQ2 : Q 20 = 53) :
    P 0 + Q 0 = 116 := by
  have eq1 : 2 * 16^2 + b * 16 + c = 54 := by 
    rw [hP] at hP1
    exact hP1
  have eq2 : 2 * 20^2 + b * 20 + c = 53 := by 
    rw [hP] at hP2
    exact hP2
  have eq3 : -2 * 16^2 + d * 16 + e = 54 := by 
    rw [hQ] at hQ1
    exact hQ1
  have eq4 : -2 * 20^2 + d * 20 + e = 53 := by 
    rw [hQ] at hQ2
    exact hQ2

  simp only [pow_two] at eq1 eq2 eq3 eq4

  have eq5 : 16 * b + c = -458 := by
    linarith
  have eq6 : 20 * b + c = -747 := by
    linarith
  have eq7 : 16 * d + e = 566 := by
    linarith
  have eq8 : 20 * d + e = 853 := by
    linarith

  have hb : b = -289 / 4 := by 
    linarith
  have hc : c = 698 := by
    linarith [eq5, hb]

  have hd : d = 287 / 4 := by 
    linarith
  have he : e = -582 := by
    linarith [eq7, hd]

  have hP0 : P 0 = c := by 
    simp [hP]
  have hQ0 : Q 0 = e := by 
    simp [hQ]

  rw [hP0, hQ0]
  linarith [hc, he]