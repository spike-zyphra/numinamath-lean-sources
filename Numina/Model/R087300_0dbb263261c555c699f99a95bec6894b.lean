import Mathlib

theorem algebra_16993 {x1 x2 : ℝ} (hx1 : x1^2-3*x1+9=x1+41) (hx2 : x2^2-3*x2+9=x2+41)
    (hx12 : x1≠x2) : |x1-x2| = 12 := by
  have h1 :x1^2-4*x1-32=0:=by linarith [hx1]
  have h2 :x2^2-4*x2-32=0:=by linarith [hx2]

  have h3 : (x1 - 8) * (x1 + 4) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- x1-8=0, so x1=8, then x2=-4
    have hx1_eq8 :x1 = 8 := by linarith
    have h32 : (x2 - 8) * (x2 + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h32) with h42 h52
    · --x2=8
      have hx2_eq8 :x2 = 8 := by linarith
      exfalso
      exact hx12 (by linarith)
    · --x2=-4
      have hx2_eq_neg4 :x2 = -4 := by linarith
      rw [hx1_eq8,hx2_eq_neg4]
      norm_num [abs]
  
  · -- x1+4=0, so x1=-4, then x2=8
    have hx1_eq_neg4 :x1 = -4 := by linarith
    have h32 : (x2 - 8) * (x2 + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h32) with h42 h52
    · --x2=8
      have hx2_eq8 :x2 = 8 := by linarith
      rw [hx1_eq_neg4,hx2_eq8]
      norm_num [abs]
    
    · --x2=-4
      have hx2_eq_neg4 :x2 = -4 := by linarith
      exfalso
      exact hx12 (by linarith)