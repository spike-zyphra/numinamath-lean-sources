import Mathlib

theorem algebra_92937 {A B C D E F G H : ℝ}
(hC : C = 5) (hsum : A + B + C = 30 ∧ B + C + D = 30 ∧ C + D + E = 30 ∧ D + E + F = 30 ∧ E + F + G = 30 ∧ F + G + H = 30) :
A + H = 25 := by
  rcases hsum with ⟨h1, h2, h3, h4, h5, h6⟩
  rw [hC] at h1 h2 h3
  have hA : A + B = 25 := by linarith
  have hB : B + D = 25 := by linarith
  have hA_eq_D : A = D := by 
    linarith
  have hD_eq_A : D = A := by linarith
  have hF : F = 5 := by
    have h4' : D + E + F = 30 := by linarith
    have h3' : D + E = 25 := by 
      linarith
    linarith [h3', h4']
  have hG : G = A := by
    have h5' : E + F + G = 30 := by linarith
    have h5_eq : E + G = 25 := by 
      rw [hF] at h5'
      linarith
    have hE_A : E + A = 25 := by 
      have h3_eq : 5 + D + E = 30 := by linarith
      rw [hD_eq_A] at h3_eq
      linarith
    linarith [h5_eq, hE_A]
  have h6' : F + G + H = 30 := by linarith
  rw [hF, hG] at h6'
  linarith