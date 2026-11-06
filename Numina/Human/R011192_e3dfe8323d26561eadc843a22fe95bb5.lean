import Mathlib
open Real Set
/-8. II 2 (NET 3) ${ }^{\mathrm{IMO} 5}$ If $a, b, c, d$ are arbitrary positive real numbers, find all possible values of  $$ S=\frac{a}{a+b+d}+\frac{b}{a+b+c}+\frac{c}{b+c+d}+\frac{d}{a+c+d} . $$-/
theorem Other_25033 (S  a b c d : ℝ) (hS : S = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d))
(ha : 0 < a) 
(hb : 0 < b) 
(hc : 0 < c) 
(hd : 0 < d) :
S ∈ Ioo 1 2 := by 
  rw [hS]
  constructor
  · -- First part: prove that $S > 1$
    have h1 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
      have h11 : 0 < a + b + d := by linarith
      have h21 : 0 < a + b + c := by linarith
      have h31 : 0 < b + c + d := by linarith
      have h41 : 0 < a + c + d := by linarith
      have h12 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 > 0 := by 
        have h2 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 1 =
            (a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
          field_simp
          ring
        rw [h2]
        have pos_num : a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) > 0 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb ha, mul_pos hb hc, mul_pos hb hd, mul_pos hc ha, mul_pos hc hb, mul_pos hc hd, mul_pos hd ha, mul_pos hd hb, mul_pos hd hc, 
                    mul_pos ha (show 0 < a + b + c by linarith), mul_pos ha (show 0 < a + b + d by linarith), mul_pos ha (show 0 < a + c + d by linarith),
                    mul_pos hb (show 0 < a + b + c by linarith), mul_pos hb (show 0 < b + c + d by linarith),
                    mul_pos hc (show 0 < b + c + d by linarith), mul_pos hc (show 0 < a + c + d by linarith),
                    mul_pos hd (show 0 < a + c + d by linarith)]
        have pos_den : (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) > 0 := by 
          positivity
        exact div_pos pos_num pos_den
      linarith
    linarith
  · -- Second part: prove that $S < 2$
    have h2 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
      have h11 : 0 < a + b + d := by linarith
      have h21 : 0 < a + b + c := by linarith
      have h31 : 0 < b + c + d := by linarith
      have h41 : 0 < a + c + d := by linarith
      have h21 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 < 0 := by
        have h3 : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) - 2 =
            (a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) / ((a + b + d) * (a + b + c) * (b + c + d) * (a + c + d)) := by 
          field_simp
          ring
        rw [h3]
        have neg_num : a * (a + b + c) * (b + c + d) * (a + c + d) + b * (a + b + d) * (b + c + d) * (a + c + d) + c * (a + b + d) * (a + b + c) * (a + c + d) + d * (a + b + d) * (a + b + c) * (b + c + d) - 2 * (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) < 0 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb ha, mul_pos hb hc, mul_pos hb hd, mul_pos hc ha, mul_pos hc hb, mul_pos hc hd, mul_pos hd ha, mul_pos hd hb, mul_pos hd hc,
                    mul_pos ha (show 0 < a + b + c by linarith), mul_pos ha (show 0 < a + b + d by linarith), mul_pos ha (show 0 < a + c + d by linarith),
                    mul_pos hb (show 0 < a + b + c by linarith), mul_pos hb (show 0 < b + c + d by linarith),
                    mul_pos hc (show 0 < b + c + d by linarith), mul_pos hc (show 0 < a + c + d by linarith),
                    mul_pos hd (show 0 < a + c + d by linarith)]
        have pos_den : (a + b + d) * (a + b + c) * (b + c + d) * (a + c + d) > 0 := by 
          positivity
        exact div_neg_of_neg_of_pos neg_num pos_den
      linarith
    linarith
