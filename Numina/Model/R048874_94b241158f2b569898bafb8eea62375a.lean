import Mathlib

theorem algebra_5024 {G : ℝ → ℝ} (hG : ∃ p q r s : ℝ, G = fun x => p*x^3 + q*x^2 + r*x + s)
    (hG1 : G 1 = 21) (hG2 : G 3 = 25) (hG3 : G 5 = 45) (hG4 : G 7 = 129) :
    G 9 = 325 := by
  rcases hG with ⟨p, q, r, s, hG_def⟩
  have eq1 : p * 1^3 + q * 1^2 + r * 1 + s = 21 := by 
    rw [hG_def] at hG1
    simpa using hG1
  have eq2 : p * 3^3 + q * 3^2 + r * 3 + s = 25 := by 
    rw [hG_def] at hG2
    simpa using hG2
  have eq3 : p * 5^3 + q * 5^2 + r * 5 + s = 45 := by 
    rw [hG_def] at hG3
    simpa using hG3
  have eq4 : p * 7^3 + q * 7^2 + r * 7 + s = 129 := by 
    rw [hG_def] at hG4
    simpa using hG4
  have eq5 : 26 * p + 8 * q + 2 * r = 4 := by
    linarith [eq1, eq2]
  have eq6 : 98 * p + 16 * q + 2 * r = 20 := by
    linarith [eq2, eq3]
  have eq7 : 218 * p + 24 * q + 2 * r = 84 := by
    linarith [eq3, eq4]
  have eq8 : 72 * p + 8 * q = 16 := by
    linarith [eq5, eq6]
  have eq9 : 120 * p + 8 * q = 64 := by
    linarith [eq6, eq7]
  have hp : p = 1 := by
    linarith [eq8, eq9]
  have hq : q = -7 := by
    linarith [eq8, hp]
  have hr : r = 17 := by
    rw [hp, hq] at eq5
    linarith
  have hs : s = 10 := by
    rw [hp, hq, hr] at eq1
    linarith
  have hG9 : G 9 = p * 9^3 + q * 9^2 + r * 9 + s := by 
    rw [hG_def]
  rw [hG9]
  rw [hp, hq, hr, hs]
  norm_num