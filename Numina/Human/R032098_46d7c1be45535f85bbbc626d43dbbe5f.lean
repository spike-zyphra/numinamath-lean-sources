import Mathlib
open Polynomial Complex

/- If $P(x)$, $Q(x)$, $R(x)$, and $S(x)$ are all polynomials such that $$P(x^5) + xQ(x^5) + x^2R(x^5) = (x^4 + x^3 + x^2 + x + 1)S(x),$$ prove that $x-1$ is a factor of $P(x)$. -/

theorem algebra_96098 {P Q R S : Polynomial Complex} (h : ∀ x : Complex, P.eval (x^5) + x * Q.eval (x^5) + x^2 * R.eval (x^5) = (x^4 + x^3 + x^2 + x + 1) * S.eval x) :(P.eval 1 = 0) := by
  have aux (x:Complex) (hx:x≠1):x^4+x^3+x^2+x+1=(x^5-1)/(x-1):= by
--We know that if $x$ is not 1, then $x^4+x^3+x^2+x+1=\frac{x^5-1}{x-1}$.
    have h1: x^5-1=(x-1)*(x^4+x^3+x^2+x+1):= by ring
    rw [h1]
    replace hx:x-1≠0:= by rw[sub_ne_zero];exact hx
    field_simp
  set ξ:=(exp (2 * Real.pi * I / 5)) with xidef
--Set $\xi = e^{2\pi i/5}$, which is a primitive 5th root of unity.
  have xiprimitive:IsPrimitiveRoot ξ 5:= by
    rw[xidef]
    apply Complex.isPrimitiveRoot_exp _ (by norm_num)
--If $x$ is a primitive 5th root of unity, then $x^4+x^3+x^2+x+1=0$. This is because $x^5-1=0$, so $x^5=1$, and $x^4+x^3+x^2+x+1=\frac{x^5-1}{x-1}=0$.
  have rootofcyc (x:Complex) (hx:IsPrimitiveRoot x 5):x^4+x^3+x^2+x+1=0:= by
    have :x-1≠0:=by
      apply IsPrimitiveRoot.sub_one_ne_zero (show 1<5 by norm_num) hx
    rw[aux]
    suffices x^5-1=0 by rw[this,zero_div]
    rw[sub_eq_zero]
    rw[hx.1]
    rw[←sub_ne_zero];exact this
  have evalxi (ξ:Complex) (hxi:IsPrimitiveRoot ξ 5):(P.eval 1)+ξ*(Q.eval 1)+ξ^2*(R.eval 1)=0:=by
--We evaluate the equation at a primitive 5-th root of unity.
    have hevalxi:=h ξ
    rw[rootofcyc ξ hxi] at hevalxi
    rw[hxi.1,zero_mul] at hevalxi
    rw[hevalxi]
--Because $\xi$ is a primitive 5th root of unity, so does $\xi^2$ and $\xi^3$.
  have xisq:IsPrimitiveRoot (ξ^2) 5:=by
    rw[IsPrimitiveRoot.pow_iff_coprime xiprimitive (by norm_num)]
    decide
  have xipow3:IsPrimitiveRoot (ξ^3) 5:=by
    rw[IsPrimitiveRoot.pow_iff_coprime xiprimitive (by norm_num)]
    decide
  have exi:=evalxi ξ xiprimitive
  have exi2:=evalxi (ξ^2) xisq
  have exi3:=evalxi (ξ^3) xipow3
--We evaluate the equation at $\xi,\xi^2$ and $\xi^3$.
  have aux:(ξ^3)^2=ξ:=by
    rw[←pow_mul,show 3*2=1+5 by rfl,pow_add,pow_one,xiprimitive.1,mul_one]
  rw[←pow_mul,show (2*2=4) by rfl] at exi2
  rw[aux] at exi3
  have eq1:(ξ^2-ξ)*(eval 1 Q)+(ξ^4-ξ^2)*(eval 1 R)=0:=by
--Subtracting the equation evaluated at $\xi$ from the equation evaluated at $\xi^2$ gives us $(\xi^2-\xi)Q(1)+(\xi^4-\xi^2)R(1)=0$.
    linear_combination' 1*exi2-1*exi
  have eq2:(ξ^3-ξ)*(eval 1 Q)+(ξ-ξ^2)*(eval 1 R)=0:=by
--Subtracting the equation evaluated at $\xi$ from the equation evaluated at $\xi^3$ gives us $(\xi^3-\xi)Q(1)+(\xi-\xi^2)R(1)=0$.
    linear_combination' 1*exi3-1*exi
  have h1:ξ^2-ξ≠0:=by
    rw[show (ξ^2-ξ)=ξ*(ξ-1) by ring,mul_ne_zero_iff]
    constructor
    apply IsPrimitiveRoot.ne_zero xiprimitive (by norm_num)
    apply IsPrimitiveRoot.sub_one_ne_zero (by norm_num) xiprimitive
  have h2:ξ^4-ξ^2≠0:=by
    rw[show (ξ^4-ξ^2)=ξ^2*(ξ^2-1) by ring,mul_ne_zero_iff]
    constructor
    apply IsPrimitiveRoot.ne_zero xisq (by norm_num)
    apply IsPrimitiveRoot.sub_one_ne_zero (by norm_num) xisq
  have evqeqzero:eval 1 Q=0:=by
--We prove that $Q(1)=0$.
    rw[show ξ^3-ξ=ξ*(ξ-1)*(ξ+1) by ring,show (ξ-ξ^2)=-((ξ)*(ξ-1)) by ring] at eq2
    rw[show ξ^2-ξ=ξ*(ξ-1) by ring,show (ξ^4-ξ^2)=ξ^2*(ξ-1)*(ξ+1) by ring] at eq1
    replace eq2:(ξ+1)*(eval 1 Q)=eval 1 R:=by
--By eq2, we have $(\xi+1)Q(1)=R(1)$.
      rw[neg_mul,←sub_eq_add_neg] at eq2
      rw[mul_assoc,mul_assoc,mul_assoc] at eq2
      rw[←mul_sub,←mul_sub] at eq2
      simp[IsPrimitiveRoot.ne_zero xiprimitive (by norm_num)] at eq2
      simp[IsPrimitiveRoot.sub_one_ne_zero (by norm_num) xiprimitive,sub_eq_zero] at eq2
      rw[eq2]
--Substracting above equation into eq1, then we get the explicit result of $Q(1)$.
    rw[←eq2,←mul_assoc,←add_mul] at eq1
    rw[show (ξ * (ξ - 1) + ξ^2 * (ξ - 1) * (ξ + 1) * (ξ + 1))=ξ * (ξ - 1) *(1+ ξ * (ξ + 1) * (ξ + 1)) by ring_nf] at eq1
    rw[mul_eq_zero_iff_left] at eq1
    exact eq1
--Because the coefficient of $Q(1)$ in the above relation is not zero, we have $Q(1)=0$.
    apply mul_ne_zero;apply mul_ne_zero
    apply IsPrimitiveRoot.ne_zero xiprimitive (by norm_num)
    apply IsPrimitiveRoot.sub_one_ne_zero (by norm_num) xiprimitive
    ring_nf
    have h4:=rootofcyc ξ xiprimitive
    rw[show ξ^4+ξ^3+ξ^2+ξ+1=(1+ξ+ξ^2*2+ξ^3)*(ξ-1)+2*ξ^2+ξ+2 by ring] at h4
    by_contra! h'
    rw[h',zero_mul,zero_add] at h4
    rw[show (1+ξ+ξ^2*2+ξ^3)=(2*ξ^2+ξ+2)*(ξ/2 +3/4)-3/4*ξ-1/2 by ring,h4,zero_mul,zero_sub,sub_eq_zero,neg_eq_iff_eq_neg] at h'
    norm_cast at h'
    field_simp at h'
    have h'':ξ=-2/3:=by
      rw[show ξ=(1/6)*(3*ξ*2) by ring,h']
      norm_num
    have h''':ξ^5=1:=by exact xiprimitive.1
    rw[h''] at h'''
    norm_num at h'''
  rw[evqeqzero,mul_zero,zero_add] at eq1
  rw[mul_eq_zero] at eq1
--Because $Q(1)=0$, we have $R(1)=0$.
  simp only [h2, false_or] at eq1
--Because $Q(1)=R(1)=0$, we know that $P(1)=0$.
  rw[eq1,evqeqzero,mul_zero,mul_zero,add_zero,add_zero] at exi
  rw[exi]