import Mathlib

open Real Polynomial
/-The equation $2^{333x-2}+2^{111x+2}=2^{222x+1}+1$ has three real roots. Given that their sum is m/n where m and n are relatively prime positive integers, find m+n.-/
theorem AIME_Algebra_727 (x y z : ℝ ) (xyzne:x<y ∧ y<z) (hx: ((2:ℝ)^(333*x-2))+2^(111*x+2)= (2^((222*x)+1))+1) (hy: ((2:ℝ)^(333*y-2))+2^(111*y+2)= (2^((222*y)+1))+1) (hz: ((2:ℝ)^(333*z-2))+2^(111*z+2)= (2^((222*z)+1))+1) (m n: ℕ ) (_:0<m) (npos:0<n) (mncoprime: Nat.Coprime m n) (hmn:(m:ℝ)/(n:ℝ)=x+y+z):m+n=113:=by
  have aux:(333:ℝ)=3*111∧(222:ℝ)=2*111:=by norm_num
--We show that x,y,z gives three real numbers p,q and r respectively, and p,q,r are distinct roots of a polynomial.
  set p:=(2:ℝ)^(111*x) with pdef
  set q:=(2:ℝ)^(111*y) with qdef
  set r:=(2:ℝ)^(111*z) with rdef
--We denote this polynomial of degree three by cub, we prove that it has roots {p,q,r}.
  set cub:=Cubic.mk (1:ℝ) (-8) (16) (-4) with cubdef
  rw[rpow_sub,rpow_add,rpow_add,aux.1,aux.2,mul_assoc,mul_comm,rpow_mul] at hx hy hz
--We deduce hp,hq,hr by hx,hy and hz.
  have hp:p^3- 8*(p^2)+16*p - 4=0:=by
    rw[←sub_eq_zero,←pdef,mul_assoc,mul_comm 2,rpow_mul,←pdef] at hx
    field_simp at hx
    rw[←hx,mul_add,mul_assoc,sub_add_eq_sub_sub,mul_comm (2^2),mul_comm (2^2) (p^2*2),mul_assoc]
    norm_num;ring_nf
    rw[mul_comm x,←pdef,←rpow_natCast,←rpow_natCast]
    simp only [Nat.cast_ofNat, rpow_two]
    simp only [Nat.ofNat_nonneg]
  have hq:q^3- 8*(q^2)+16*q - 4=0:=by
    rw[←sub_eq_zero,←qdef,mul_assoc,mul_comm 2,rpow_mul,←qdef] at hy
    field_simp at hy
    rw[←hy,mul_add,mul_assoc,sub_add_eq_sub_sub,mul_comm (2^2),mul_comm (2^2) (q^2*2),mul_assoc]
    norm_num;ring_nf
    rw[mul_comm y,←qdef,←rpow_natCast,←rpow_natCast]
    simp only [Nat.cast_ofNat, rpow_two,Nat.ofNat_nonneg]
    simp only [Nat.ofNat_nonneg]
  have hr:r^3- 8*(r^2)+16*r - 4=0:=by
    rw[←sub_eq_zero,←rdef,mul_assoc,mul_comm 2,rpow_mul,←rdef] at hz
    field_simp at hz
    rw[←hz,mul_add,mul_assoc,sub_add_eq_sub_sub,mul_comm (2^2),mul_comm (2^2) (r^2*2),mul_assoc]
    norm_num;ring_nf
    rw[mul_comm z,←rdef,←rpow_natCast,←rpow_natCast]
    simp only [Nat.cast_ofNat, rpow_two,Nat.ofNat_nonneg]
    simp only [Nat.ofNat_nonneg]
--As fun x=>2^x is monotone, we know that p< q < r.
  have pqrne:p<q ∧ q<r:=by
    rw[pdef,qdef,rdef]
    constructor
    · apply Real.rpow_lt_rpow_of_exponent_lt _ (by linarith)
      linarith
    · apply Real.rpow_lt_rpow_of_exponent_lt _ (by linarith)
      linarith
  replace pqrne:p≠q∧p≠r∧q≠r:=by
    constructor
    linarith
    constructor
    linarith
    linarith
  set s := ({p, q, r} : Finset ℝ) with sdef
--We prove that s have cardinality 3.
  have scard:Finset.card s =3:=by
    apply Finset.card_eq_three.mpr
    use p,q,r
    constructor
    exact pqrne.1
    constructor
    exact pqrne.2.1
    constructor
    exact pqrne.2.2
    rfl
--By the definition of cub, we can expand it.
--As we know the three distinct roots of cub, it has another form.
  have cubex:cub.toPoly=(X-C p)*(X-C q)*(X-C r) :=by
--Because they have the same leading coefficients. And they have the same value at p,q,r. We know that they are the same.
    apply Polynomial.eq_of_degree_le_of_eval_finset_eq s
    · simp only [scard,ne_eq, one_ne_zero, not_false_eq_true, Cubic.degree_of_a_ne_zero,Nat.ofNat_le_cast,le_rfl]
    · simp;norm_num
    · simp
    · rintro a ha
      rw[sdef] at ha
      simp
--Because a∈{p,q,r}, we know a=p or a=q or a=r
      replace ha:a=p∨a=q∨a=r:=by
        rw[←Finset.mem_coe] at ha
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,Set.mem_singleton_iff] at ha
        exact ha
      rcases ha with ha | ha | ha
      repeat(rw[ha];simp only [sub_self, zero_mul,cub,Cubic.toPoly,map_one, one_mul, map_neg, neg_mul, eval_add, eval_pow, eval_X, eval_neg, eval_mul,eval_C];linarith)
--Comparing the constant term, we get -pqr=-4. This is Vieta's formula
  have prod4:-p*q*r=-4:=by
      have :cub.toPoly.coeff 0=-p*q*r:=by
        rw[cubex];simp
      rw[←this]
      simp[cub]
--Substitute the definition of p,q,r and use the fact that x=>2^x is injective.
  have xyzsum:111*x+111*y+111*z=2:=by
    simp[pdef,qdef,rdef] at prod4
    have aux1:(2:ℝ)^(111*x+111*y+111*z) = 2^2:=by
      rw[pow_two]
      norm_num
      rw[←prod4]
      rw[rpow_add,rpow_add]
      all_goals
      · norm_num
    calc
      111 * x + 111 * y + 111 * z=logb 2 ((2:ℝ)^(111*x+111*y+111*z)):=by
        simp
      _=logb 2 ((2:ℝ)^2):=by rw[aux1]
      _=2:= by
        rw[logb_pow]
        simp only [Nat.cast_ofNat, Nat.one_lt_ofNat, logb_self_eq_one, mul_one]
--We know that x,y,z are positive.
--We clear irrelevant goals.
  all_goals
    try simp only [Nat.ofNat_nonneg,Nat.ofNat_pos]
  rw[←mul_add,←mul_add] at xyzsum
--We know that x+y+z=2/111=m/n. As m,n are coprime, we should have m=2 and n=111
  replace xyzsum:x+y+z=2/111:=by linarith
  rw[xyzsum] at hmn
  replace hmn :(m:ℚ)/n=2/111:=by
    field_simp
    field_simp at hmn
    norm_cast
    norm_cast at hmn
  have nintpos:0<(n:ℤ):=by linarith
  have h:(m:ℤ).natAbs.Coprime (n:ℤ).natAbs:=by simp;exact mncoprime
--Because m n are coprime, we know that (m/n).den=n and (m/n).num=m.
  have h':=(Rat.num_div_eq_of_coprime nintpos h)
  have h'':=(Rat.den_div_eq_of_coprime nintpos h)
  simp only [Int.cast_natCast, Nat.cast_inj] at h' h''
  rw[hmn] at h' h''
--Substitue m,n to get the final answer 2+111=113.
  suffices m=2∧ n=111 by
    rw[this.1,this.2]
  rw[show (2:ℚ)/111=((2:ℤ):ℚ)/(111:ℤ) by simp only [Int.cast_ofNat],Rat.num_div_eq_of_coprime] at h'
  rw[show (2:ℚ)/111=((2:ℤ):ℚ)/(111:ℤ) by simp only [Int.cast_ofNat],←Int.natCast_inj,Rat.den_div_eq_of_coprime] at h''
  norm_cast at h' h''
  rw[h',h'']
--Clean up irrelevant goals.
  simp only [and_self]
  norm_num
  decide
  norm_num
  decide