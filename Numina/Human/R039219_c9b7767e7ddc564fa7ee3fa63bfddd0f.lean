import Mathlib

open Real

/- 2. In $\triangle A B C$, prove:

$$

\frac{a}{b+c-a}+\frac{b}{c+a-b}+\frac{c}{a+b-c} \geqslant \frac{b+c-a}{a}+\frac{c+a-b}{b}+\frac{a+b-c}{c} \geqslant 3 .

$$
 -/
theorem inequalities_244561 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : c + a > b) (h'' : b + c > a) :
    3 ≤ (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ∧
    (b + c - a) / a + (c + a - b) / b + (a + b - c) / c ≤
    a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
    split_ands
    {
        -- Notice that, (b+c-a)/a=(b+c+a)/a-2
        have habc_aux (a':ℝ) (b':ℝ) (c':ℝ) (ha':0<a') : (b'+c'-a')/a' = (b'+c'+a')/a' - 2 := by rw [sub_div,add_div _ a',div_self (ne_of_lt ha').symm];ring
        have hbca := habc_aux b c a hb
        have hcab := habc_aux c a b hc
        have habc := habc_aux a b c ha

        rw [hbca,habc,hcab]

        have h_temp : (b + c + a) / a - 2 + ((c + a + b) / b - 2) + ((a + b + c) / c - 2) = (a+b+c)*(1/a+1/b+1/c)-6 := by ring

        rw [h_temp]

        -- We apply the Cauchy-Schwarz inequality to get the inequality 9 ≤ (a+b+c)*(1/a+1/b+1/c)
        have hCS : 9 ≤ (a+b+c)*(1/a+1/b+1/c) := by
            let v : EuclideanSpace ℝ (Fin 3) := ![sqrt a,sqrt b,sqrt c]
            let w : EuclideanSpace ℝ (Fin 3) := ![1/sqrt a,1/sqrt b,1/sqrt c]
            have hvw := abs_real_inner_le_norm v w
            simp [v, w,Fin.sum_univ_succ,EuclideanSpace.norm_eq] at hvw
            field_simp at hvw
            norm_num at hvw
            rw [←sq_le_sq₀ zero_le_three] at hvw
            simp [div_pow,mul_pow] at hvw
            rw [sq_sqrt,sq_sqrt,sq_sqrt (le_of_lt ha),sq_sqrt (le_of_lt hb),sq_sqrt (le_of_lt hc)] at hvw
            have h_aux : (a + (b + c)) * (b * c + (c + b) * a) / (a * (b * c)) = (a+b+c)*(1/a+1/b+1/c) := by field_simp; ring
            norm_num at hvw
            rwa [h_aux] at hvw
            -- Resolving the unproven nonneg properties
            exact add_nonneg (mul_nonneg (le_of_lt hb) (le_of_lt hc)) (mul_nonneg (add_nonneg (le_of_lt hc) (le_of_lt hb)) (le_of_lt ha))
            exact add_nonneg (le_of_lt ha) (add_nonneg (le_of_lt hb) (le_of_lt hc))
            exact div_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (mul_nonneg (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)))


        have hCS' :=tsub_le_tsub_right hCS 6
        norm_num at hCS'
        norm_num
        exact hCS'
    }
    {
        let x:=(b+c-a)/2
        let y:=(c+a-b)/2
        let z:=(a+b-c)/2
        have hx:b+c-a=2*x := by ring
        have hy:c+a-b=2*y := by ring
        have hz:a+b-c=2*z := by ring
        have hxp:0<x:=half_pos (sub_pos.2 h'')
        have hyp:0<y:=half_pos (sub_pos.2 h')
        have hzp:0<z:=half_pos (sub_pos.2 h)
        have ha:a=y+z:=by ring
        have hb:b=z+x:=by ring
        have hc:c=x+y:=by ring

        -- Rewrite in term of x, y and z
        rw [hx,hy,hz,ha,hb,hc]
        apply le_of_mul_le_mul_left (a:=2) _ (zero_lt_two)
        have h_temp : 2 * (2 * x / (y + z) + 2 * y / (z + x) + 2 * z / (x + y))
            = 4 * x / (y + z) + 4 * y / (z + x) + 4 * z / (x + y) := by ring
        have h_temp' : 2 * ((y + z) / (2 * x) + (z + x) / (2 * y) + (x + y) / (2 * z))
            = (y + z) / x + (z + x) / y + (x + y) / z := by
            rw [mul_add 2,mul_add 2,mul_div 2,mul_div 2 (z+x),mul_div 2 (x+y)]
            simp [mul_div_mul_left]

        rw [h_temp,h_temp']

        -- We apply the Cauchy-Schwarz inequality to get the inequality 4 ≤ (x'/y'+x'/z')*(y'/x'+z'/x')
        have hCS (x' y' z' : ℝ) (hx' : 0 < x') (hy' : 0 < y') (hz' : 0 < z'): 4 ≤ (x'/y'+x'/z')*(y'/x'+z'/x') := by
            let v : EuclideanSpace ℝ (Fin 2) := ![sqrt (x'/y'),sqrt (x'/z')]
            let w : EuclideanSpace ℝ (Fin 2) := ![sqrt (y'/x'),sqrt (z'/x')]
            have hvw := abs_real_inner_le_norm v w
            simp [v, w,EuclideanSpace.norm_eq] at hvw
            field_simp at hvw
            norm_num at hvw
            rw [←sq_le_sq₀ zero_le_two] at hvw
            simp [div_pow,mul_pow] at hvw
            rw [sq_sqrt,sq_sqrt,sq_sqrt (le_of_lt hy'),sq_sqrt (le_of_lt hz'),sq_sqrt (le_of_lt hx')] at hvw
            norm_num at hvw
            have h_aux : (x' * z' + x' * y') * (y' + z') / (y' * z' * x') = (x' / y' + x' / z') * (y' / x' + z' / x') := by field_simp
            rwa [h_aux] at hvw
            -- Resolving the unproven nonneg properties
            exact add_nonneg (le_of_lt hy') (le_of_lt hz')
            exact add_nonneg (mul_nonneg (le_of_lt hx') (le_of_lt hz')) (mul_nonneg (le_of_lt hx') (le_of_lt hy'))
            exact div_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (mul_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (sqrt_nonneg _))


        have hCS' (x' y' z' : ℝ) (hx' : 0 < x') (hy' : 0 < y') (hz' : 0 < z'): 4*x' / (y' + z') ≤ x'/y' + x'/z':= by
            rw [←mul_div 4]
            apply (le_div_iff₀ _).1
            have h_aux : (x' / y' + x' / z') / (x' / (y' + z')) = (x' / y' + x' / z') * (y' / x' + z' / x') := by field_simp
            rw [h_aux]; exact hCS x' y' z' hx' hy' hz'
            exact div_pos hx' (add_pos hy' hz')


        have hCSx := hCS' x y z hxp hyp hzp
        have hCSy := hCS' y z x hyp hzp hxp
        have hCSz := hCS' z x y hzp hxp hyp

        -- We add the three inequalities
        have hCSxyz := add_le_add (add_le_add hCSx hCSy) hCSz

        have h_temp'' :  x / y + x / z + (y / z + y / x) + (z / x + z / y) =(y + z) / x + (z + x) / y + (x + y) / z := by ring

        rwa [h_temp''] at hCSxyz
    }