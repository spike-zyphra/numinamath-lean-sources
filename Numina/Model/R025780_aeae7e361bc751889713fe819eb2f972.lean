import Mathlib

theorem algebra_103437 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / (a + b + c) = 1 / a + 1 / b + 1 / c) (h' : a + b + c ≠ 0) :
    |a| = |b| ∨ |b| = |c| ∨ |a| = |c| := by
  have eq1 : a * b * c = (a + b + c) * (a * b + a * c + b * c) := by
    field_simp [h', ha, hb, hc] at h ⊢
    nlinarith
  have h1 : (a + b) * (b + c) * (c + a) = 0 := by
    nlinarith 
       

  
  cases' (mul_eq_zero.1 h1) with h2 h3 
  cases' (mul_eq_zero.1 h2) with h4 h5
  · -- Case where a + b = 0.
    left 
    have ha1 : a = -b := by linarith
    have ha1b1c1 : |a| = |b| := by 
      rw [ha1]
      simp [abs_neg]
    exact_mod_cast ha1b1c1 
  · -- Case where b + c = 0.
    right 
    left 
    have hb1 : b = -c := by linarith 
    have hb1c1 : |b| = |c| := by 
      rw [hb1]
      simp [abs_neg]
    exact_mod_cast hb1c1 
  · -- Case where c + a = 0.
    right
    right 
    have hb2 : a = -c := by linarith 
    have hb2c2 : |a| = |c| := by
      rw [hb2]
      simp [abs_neg]
    exact_mod_cast hb2c2