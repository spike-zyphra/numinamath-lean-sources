import Mathlib

open Polynomial
/-Determine x^2+y^2+z^2+w^2if
$\frac{x^2}{2^2-1}+\frac{y^2}{2^2-3^2}+\frac{z^2}{2^2-5^2}+\frac{w^2}{2^2-7^2}=1,
\frac{x^2}{4^2-1}+\frac{y^2}{4^2-3^2}+\frac{z^2}{4^2-5^2}+\frac{w^2}{4^2-7^2}=1,
\frac{x^2}{6^2-1}+\frac{y^2}{6^2-3^2}+\frac{z^2}{6^2-5^2}+\frac{w^2}{6^2-7^2}=1,
\frac{x^2}{8^2-1}+\frac{y^2}{8^2-3^2}+\frac{z^2}{8^2-5^2}+\frac{w^2}{8^2-7^2}=1$-/
theorem AIME_Algebra_94591 {x y z w : ℝ}
(h1 : x^2 / (2^2 - 1) + y^2 / (2^2 - 3^2) + z^2 / (2^2 - 5^2) + w^2 / (2^2 - 7^2) = 1)
(h2 : x^2 / (4^2 - 1) + y^2 / (4^2 - 3^2) + z^2 / (4^2 - 5^2) + w^2 / (4^2 - 7^2) = 1)
(h3 : x^2 / (6^2 - 1) + y^2 / (6^2 - 3^2) + z^2 / (6^2 - 5^2) + w^2 / (6^2 - 7^2) = 1)
(h4 : x^2 / (8^2 - 1) + y^2 / (8^2 - 3^2) + z^2 / (8^2 - 5^2) + w^2 / (8^2 - 7^2) = 1) :
x^2 + y^2 + z^2 + w^2 = 36 := by
--We prove a lemma that degree of (constant*polynomial) is no greater than the second factor.
  have aux (x:Real) (po:Polynomial Real): ((C x)* po).degree≤ po.degree:=by
    by_cases h:x=0
    rw[h]
    simp only [map_zero, zero_mul, degree_zero, bot_le]
    rw[degree_C_mul h]
--We introduce several product of linear polynomials.
  set p1:Polynomial Real:=(X-C (3^2))*(X-C (5^2))*(X-C (7^2)) with p1def
  set p3:Polynomial Real:=(X-C (1^2))*(X-C (5^2))*(X-C (7^2)) with p3def
  set p5:Polynomial Real:=(X-C (1^2))*(X-C (3^2))*(X-C (7^2)) with p5def
  set p7:Polynomial Real:=(X-C (1^2))*(X-C (3^2))*(X-C (5^2)) with p7def
--The polynomial occurs when we clear the denominators is denoted by f.
  set f:Polynomial Real:=(X-C (1^2))*(X-C (3^2))*(X-C (5^2))*(X-C (7^2)) with fdef
--The polynomial f has degree 4.
  have degf:f.degree=4:=by
    rw[fdef,degree_mul,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C]
    rfl
--The polynomial f has leading coefficient 1.
  have leadf:f.leadingCoeff=1:=by
    rw[fdef]
    simp only [leadingCoeff_mul,leadingCoeff_X_sub_C,mul_one]
--Each pi has degree 3.
  have degp1:p1.degree=3:=by
    rw[p1def,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C]
    rfl
  have degp3:p3.degree=3:=by
    rw[p3def,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C]
    rfl
  have degp5:p5.degree=3:=by
    rw[p5def,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C]
    rfl
  have degp7:p7.degree=3:=by
    rw[p7def,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C]
    rfl
--Clear the denominators at h1.
  replace h1:x^2*(eval (2^2) p1)+y^2*(eval (2^2) p3)+z^2*(eval (2^2) p5)+w^2*(eval (2^2) p7)=eval (2^2) f :=by
    rw[p1def,p3def,p5def,p7def,fdef]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_ofNat, one_pow, eval_one,Polynomial.eval_C]
    field_simp at h1
    linarith[h1]
--Clear the denominators at h2.
  replace h2:x^2*(eval (4^2) p1)+y^2*(eval (4^2) p3)+z^2*(eval (4^2) p5)+w^2*(eval (4^2) p7)=eval (4^2) f :=by
    rw[p1def,p3def,p5def,p7def,fdef]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_ofNat, one_pow, eval_one,Polynomial.eval_C]
    field_simp at h2
    linarith[h2]
--Clear the denominators at h3.
  replace h3:x^2*(eval (6^2) p1)+y^2*(eval (6^2) p3)+z^2*(eval (6^2) p5)+w^2*(eval (6^2) p7)=eval (6^2) f :=by
    rw[p1def,p3def,p5def,p7def,fdef]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_ofNat, one_pow, eval_one,Polynomial.eval_C]
    field_simp at h3
    linarith[h3]
--Clear the denominators at h4.
  replace h4:x^2*(eval (8^2) p1)+y^2*(eval (8^2) p3)+z^2*(eval (8^2) p5)+w^2*(eval (8^2) p7)=eval (8^2) f :=by
    rw[p1def,p3def,p5def,p7def,fdef]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_ofNat, one_pow, eval_one,Polynomial.eval_C]
    field_simp at h4
    linarith[h4]
--The polynomial on the lefthand side of h1,h2,h3,h4 is denoted by g.
  set g:Polynomial Real:= (C (x^2))*p1+C (y^2) *p3+C (z^2)*p5+C (w^2)*p7 with gdef
--The polynomial g has degree at most 3.
  have degg:g.degree≤3:=by
    rw[gdef]
    apply degree_add_le_of_degree_le
    apply degree_add_le_of_degree_le
    apply degree_add_le_of_degree_le
    all_goals
      simp only [Nat.cast_ofNat]
    · rw[←degp1];apply aux
    · rw[←degp3];apply aux
    · rw[←degp5];apply aux
    · rw[←degp7];apply aux
  replace h1 :eval (2^2) g=eval (2^2) f:=by
    rw[gdef,←h1]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
  replace h2 :eval (4^2) g=eval (4^2) f:=by
    rw[gdef,←h2]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
  replace h3 :eval (6^2) g=eval (6^2) f:=by
    rw[gdef,←h3]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
  replace h4 :eval (8^2) g=eval (8^2) f:=by
    rw[gdef,←h4]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
--As f-g has 4 roots {2^2,4^2,6^2,8^2}, and it is monic, it equals to a monic polynomial pogoal defined here.
  set pogoal:Polynomial Real:=(X-C (2^2))*(X-C (4^2))*(X-C (6^2))*(X-C (8^2)) with pogoaldef
  set roots:Finset Real:= {2^2,4^2,6^2,8^2} with rootsdef
  have rootscard:roots.card=4:=by rw[rootsdef];norm_num
  have auxl:pogoal=f-g:=by
--We prove pogoal=f-g as they have same roots,leading cofficients, and degree.
    apply Polynomial.eq_of_degree_le_of_eval_finset_eq roots
    · rw[rootscard]
      simp only [Nat.cast_ofNat]
      rw[pogoaldef]
      norm_num
--They have the same degree.
    · rw[pogoaldef]
      rw[degree_mul,degree_mul,degree_mul,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C,degree_X_sub_C,eq_comm]
      norm_num
      rw[←degf]
      apply degree_sub_eq_left_of_degree_lt
      rw[degf]
      apply lt_of_le_of_lt degg (by norm_num)
--They have the same leadingcoefficients.
    · rw[pogoaldef]
      simp only [leadingCoeff_mul,leadingCoeff_X_sub_C,mul_one]
      symm
      rw[←leadf]
      apply leadingCoeff_sub_of_degree_lt
      rw[degf]
      apply lt_of_le_of_lt degg (by norm_num)
--They equals when evaluating at the elements of roots={2^2,4^2,6^2,8^2}
    · rw[rootsdef]
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with (hr|hr|hr|hr)
      all_goals
        rw[hr,eval_sub,pogoaldef]
        simp
        linarith
  replace auxl:g=f-pogoal:=by
    rw[auxl]
    ring
--We evaluate g=f-pogoal at 1^2
  replace h1:eval (1^2) g=- eval (1^2) pogoal:=by
    rw[auxl,eval_sub]
    simp only [sub_eq_neg_self,fdef]
    simp only [ eval_mul, eval_sub, eval_X, sub_self,eval_C, zero_mul]
--We evaluate g=f-pogoal at 3^2
  replace h2:eval (3^2) g=- eval (3^2) pogoal:=by
    rw[auxl,eval_sub]
    simp only [sub_eq_neg_self,fdef]
    simp only [ eval_mul, eval_sub, eval_X,  eval_pow, eval_C,sub_self, mul_zero, zero_mul]
--We evaluate g=f-pogoal at 5^2
  replace h3:eval (5^2) g=- eval (5^2) pogoal:=by
    rw[auxl,eval_sub]
    simp only [sub_eq_neg_self,fdef]
    simp only [ eval_mul, eval_sub, eval_X,  eval_pow, eval_C,sub_self, mul_zero, zero_mul]
--We evaluate g=f-pogoal at 7^2
  replace h4:eval (7^2) g=- eval (7^2) pogoal:=by
    rw[auxl,eval_sub]
    simp only [sub_eq_neg_self,fdef]
    simp only [ eval_mul, eval_sub, eval_X,  eval_pow, eval_C,sub_self, mul_zero, zero_mul]
--Simplify the h1,h2,h3,h4, we get linear equation on x^2,y^2,z^2 and w^2.
  rw[gdef] at h1 h2 h3 h4
  rw[p3def,p5def,p7def,pogoaldef,eq_comm] at h1
  rw[p1def,p5def,p7def,pogoaldef,eq_comm] at h2
  rw[p1def,p3def,p7def,pogoaldef,eq_comm] at h3
  rw[p1def,p3def,p5def,pogoaldef,eq_comm] at h4
  simp[p1def] at h1
  simp[p3def] at h2
  simp[p5def] at h3
  simp[p7def] at h4
  rw[←div_eq_iff,eq_comm] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  all_goals
    norm_num
--Substitute the value of x^2,y^2,z^2,w^2 and calculate the result.
  rw[h1,h2,h3,h4]
  norm_num