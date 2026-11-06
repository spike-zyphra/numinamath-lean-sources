import Mathlib

/- 2.Show that $\sqrt{\frac{a b}{(a+c)(b+c)}}+\sqrt{\frac{b c}{(b+a)(c+a)}}+\sqrt{\frac{c a}{(c+b)(b+a)}} \leq \frac{3}{2}, a, b, c>0$ -/
theorem inequalities_102694 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a * b / ((a + c) * (b + c))) +
    Real.sqrt (b * c / ((b + a) * (c + a))) +
    Real.sqrt (c * a / ((c + b) * (b + a))) ≤ 3 / 2 := by

    -- We use the AM-GM inequality to show that Real.sqrt (a * b / ((a + c) * (b + c))) ≤ 1/2 (a/(a+c) + b/(b+c)) and similarly for other two terms.
    have eq1: Real.sqrt (a * b / ((a + c) * (b + c))) = Real.sqrt ((a / (a + c))) * Real.sqrt (b/((b + c))) := by field_simp
    have eq2: Real.sqrt (b * c / ((b + a) * (c + a))) = Real.sqrt ((b / (b + a))) * Real.sqrt ((c / (c + a))) := by field_simp
    have eq3: Real.sqrt (c * a / ((c + b) * (b + a))) = Real.sqrt ((c / (c + b))) * Real.sqrt ((a / (b + a))) := by field_simp
    rw [eq1,eq2,eq3]

    have t1: Real.sqrt ((a / (a + c))) = (a/(a+c))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    have t2: Real.sqrt ((b / (b + c))) = (b/(b+c))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    have t3: Real.sqrt ((b / (b + a))) = (b/(b+a))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    have t4: Real.sqrt ((c / (c + a))) = (c/(c+a))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    have t5: Real.sqrt ((c / (c + b))) = (c/(c+b))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    have t6: Real.sqrt ((a / (b + a))) = (a/(b+a))^(1/(2:ℝ)) := by  simp [Real.sqrt_eq_rpow]
    rw [t1,t2,t3,t4,t5,t6]

    have ineq1 : (a / (a + c)) ^ (1 / (2:ℝ)) * (b / (b + c)) ^ (1 / (2:ℝ)) ≤ (1/(2:ℝ)) * (a/(a+c)) + (1/(2:ℝ)) * (b/(b+c)) := by 
      apply Real.geom_mean_le_arith_mean2_weighted
      norm_num; norm_num
      positivity; positivity
      norm_num
    have ineq2 : (b / (b + a)) ^ (1 / (2:ℝ)) * (c / (c + a)) ^ (1 / (2:ℝ)) ≤ (1/(2:ℝ)) * (b/(b+a)) + (1/(2:ℝ)) * (c/(c+a)) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      norm_num; norm_num
      positivity; positivity
      norm_num
    have ineq3 :  (c / (c + b)) ^ (1 / (2:ℝ)) * (a / (b + a)) ^ (1 / (2:ℝ)) ≤ (1/(2:ℝ)) * (c/(c+b)) + (1/(2:ℝ)) * (a/(b+a)) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      norm_num; norm_num
      positivity; positivity
      norm_num

    -- Summing all these three terms together, we get 3/2 as an upper bound.    
    have feq : (1/(2:ℝ)) * (a/(a+c)) + (1/(2:ℝ)) * (b/(b+c)) + (1/(2:ℝ)) * (b/(b+a)) + (1/(2:ℝ)) * (c/(c+a)) + (1/(2:ℝ)) * (c/(c+b)) + (1/(2:ℝ)) * (a/(b+a)) = 3/2 := by 
      have : (1/(2:ℝ)) * (a/(a+c))  +  (1/(2:ℝ)) * (c/(c+a)) = (1/(2:ℝ)) := by
        have : (1/(2:ℝ)) * (a/(a+c))  +  (1/(2:ℝ)) * (c/(c+a)) = (1/(2:ℝ)) * ((a+c)/(a+c)) := by ring
        rw[this]; field_simp
      have : (1/(2:ℝ)) * (b/(b+c))  +  (1/(2:ℝ)) * (c/(c+b)) = (1/(2:ℝ)) := by
        have : (1/(2:ℝ)) * (b/(b+c))  +  (1/(2:ℝ)) * (c/(c+b)) = (1/(2:ℝ)) * ((b+c)/(b+c)) := by ring
        rw[this]; field_simp
      have :  (1/(2:ℝ)) * (a/(b+a))  +  (1/(2:ℝ)) * (b/(b+a)) = (1/(2:ℝ)) := by
        have : (1/(2:ℝ)) * (a/(b+a))  +  (1/(2:ℝ)) * (b/(b+a)) = (1/(2:ℝ)) * ((a+b)/(a+b)) := by ring
        rw[this]; field_simp
      linarith
    
    linarith