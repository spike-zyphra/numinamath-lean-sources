import Mathlib

/- Two different positive numbers $a$ and $b$ each differ from their reciprocals by $1$. What is $a+b$? -/
theorem algebra_20885 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (h1 : |a - 1 / a| = 1) (h2 : |b - 1 / b| = 1) : a + b = Real.sqrt 5 := by

  --Use the assumption to show that a and b can only be (1 + Real.sqrt 5)/2 or (-1 + Real.sqrt 5)/2.
  --This follows from solving a quadratic equation.
  have lem: ∀ x : ℝ, 0<x → |x - 1 / x| = 1 → x = (1 + Real.sqrt 5)/2 ∨ x = (-1 + Real.sqrt 5)/2 := by
    intro x xpos hx
    have xne0: x ≠ 0 := by linarith
    rw [abs_eq] at hx; swap; linarith
    rcases hx with h | h
    
    have eq : x^2 - x - 1 = 0 := by field_simp at h ⊢; ring_nf at h ⊢; linarith
    have hroot: x= (1+Real.sqrt 5)/2 ∨ x= (1-Real.sqrt 5)/2 := by 
       have tmp : x^2 - x - 1 = (x - ((1+Real.sqrt 5)/2)) * (x - ((1-Real.sqrt 5)/2)) := by field_simp; ring_nf; field_simp; ring_nf
       rw [tmp] at eq
       have cla : (x - (1 + √5) / 2) = 0 ∨  (x - (1 - √5) / 2) =0 := by exact mul_eq_zero.mp eq
       rcases cla with c | c; left; linarith; right; linarith
    rcases hroot with ha | hb
    left; assumption
    have : x < 0 := by rw [hb]; exact goldConj_neg
    linarith

    have eq : x^2 + x - 1 = 0 := by field_simp at h ⊢; ring_nf at h ⊢; linarith
    have hroot: x= (-1+Real.sqrt 5)/2 ∨ x= (-1-Real.sqrt 5)/2 := by 
       have tmp : x^2 + x - 1 = (x - ((-1+Real.sqrt 5)/2)) * (x - ((-1-Real.sqrt 5)/2)) := by field_simp; ring_nf; field_simp; ring_nf
       rw [tmp] at eq
       have cla : (x - ((-1+Real.sqrt 5)/2)) = 0 ∨  (x - ((-1-Real.sqrt 5)/2)) =0 := by exact mul_eq_zero.mp eq
       rcases cla with c | c; left; linarith; right; linarith
    rcases hroot with ha | hb
    right; assumption
    have : x < 0 := by 
      rw [hb]
      refine div_neg_of_neg_of_pos ?_ ?_
      have : 0 < Real.sqrt 5 := by norm_num
      linarith
      linarith
    linarith

  -- Now, using the assumption that a≠b, we get a+b can only be sqrt 5.
  have aeq : a = (1 + Real.sqrt 5)/2 ∨ a = (-1 + Real.sqrt 5)/2 := by apply lem a ha h1
  have beq : b = (1 + Real.sqrt 5)/2 ∨ b = (-1 + Real.sqrt 5)/2 := by apply lem b hb h2
  cases aeq ; 
  
  cases beq
  exfalso;
  have : a = b := by linarith
  contradiction

  linarith

  cases beq
  linarith

  have : a = b := by linarith
  contradiction
