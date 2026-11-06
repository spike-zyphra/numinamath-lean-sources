import Mathlib
import Aesop

open BigOperators Finset Nat Real

/-The increasing geometric sequence x_0,x_1,x_2,… consists entirely of integral powers of 3.
 Given that ∑_{n=0}^7 log 3 x_n=308 and 56≤log_3(∑_{n=0}^7x_n)≤57 find log_3 x_{14}).-/
theorem AIME_Algebra_733 (x:ℕ → ℝ) (x0 rat: ℝ) (hrat:1<rat) (xgeo:∀ i, x i=x0*rat^i) (hx: ∀ i, ∃ (k:ℤ) , x i = 3 ^ k) (h1:∑ n ∈ range 8 , (logb 3 (x n))=308) (h2:56≤logb 3 (∑ n ∈ range 8 , x n))(h3:logb 3 (∑ n ∈ range 8 , x n)≤ 57):logb 3 (x 14)=91:=by
  have h0:x0=x 0:=by
    rw[xgeo];simp only [pow_zero, mul_one]
  have xpow:(∃ a: ℤ, x0=3^a):=by rw[h0];exact hx 0
  rcases xpow with ⟨a,ha⟩
  have rpow: ∃ (b:ℤ) ,rat=3^b:=by
    rcases hx 1 with ⟨c,hc⟩
    rw[xgeo,ha,pow_one] at hc
    use c-a
    replace hc :3^ (a:ℝ)*rat=3^(c:ℝ):=by norm_cast
    calc
      rat= 3^(a:ℝ)*3^(-a:ℝ)*rat:=by norm_cast;field_simp
        _= 3^((c:ℝ)-a):=by
          rw[mul_assoc,mul_comm,mul_assoc,mul_comm rat,hc,mul_comm]
          rw[rpow_sub]
          field_simp
          norm_cast
          rw[mul_assoc]
          field_simp
          norm_num
    norm_cast
  rcases rpow with ⟨b,hb⟩
--To find out x 14 we need to determine the whole geometric series.
--We express the sequence in terms of a and b. Then we solve the equation for a,b.
  rw[hb,ha] at xgeo
  replace h1 : (∑ n ∈ range 8, logb 3 (3^a*(3^b)^n)) = 308:=by
    rw[←h1]
    congr
    ext n
    rw[xgeo]
--We use the lemma aux to simplify the code when necessary.
  have aux (n:ℕ):logb 3 (3^a*(3^b)^n)=a+b*n:=by
    rw[logb_eq_iff_rpow_eq]
    symm
    rw[←rpow_intCast,←rpow_intCast,←rpow_natCast,← rpow_mul,rpow_add]
    all_goals try norm_num
    rw[←rpow_intCast,←rpow_intCast]
    apply mul_pos
    apply Real.rpow_pos_of_pos
    simp
    apply pow_pos
    apply rpow_pos_of_pos
    simp
  norm_cast at aux
--We rewrite the sum of geometric series into a single term which will e used in h2 and h3
  have h:∑ n ∈ range 8, 3^(a+b*n)=(3:ℝ)^a*(((3^b)^8-1)/(3^b-1)):=by
    rw[hb] at hrat
    rw[← geom_sum_eq,mul_sum]
    congr;ext n
    rw[←rpow_intCast,←rpow_intCast,←rpow_intCast,←rpow_natCast,← rpow_mul]
    rw[←rpow_add]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    all_goals linarith
--Simplify the definition of x i.
  replace xgeo:∀ (i : ℕ), x i = 3 ^ (a+b*i):=by
    intro n
    rw[xgeo,←rpow_intCast,←rpow_intCast,←rpow_intCast,←rpow_natCast,← rpow_mul]
    rw[←rpow_add]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    all_goals linarith
--We use aux to simplify the conditon h1.
  replace h1:(∑ n ∈ range 8, (a+b*n)) =(308:ℝ):=by
    rw[←h1]
    simp
    congr
    ext n
    rw[aux]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
--We substitute the form of x i in h2 and h3.
  replace h2:56 ≤ logb 3 (∑ n ∈ range 8, 3^(a+b*n)):=by
    apply le_trans h2
    apply le_of_eq
    congr
    ext n
    rw[xgeo]
  replace h3:logb 3 (∑ n ∈ range 8, 3^(a+b*n)) ≤ 57:=by
    apply le_trans' h3
    apply le_of_eq
    congr
    ext n
    rw[xgeo]
  norm_cast at h1
  rw[sum_add_distrib,←mul_sum] at h1
  simp at h1
--We find out the first equation of a,b from h1.
  replace h1:8 * a + b * ∑ i ∈ range 8, i = 308:=by
    simp[h1]
  norm_num at h1
  replace h1 :2*a+7*b=77:=by linarith
  rw[h] at h2 h3
--Some auxiliary lemmas to help linarith.
  have apowpos:0<(3:ℝ)^a:=by
    rw[←rpow_intCast]
    apply rpow_pos_of_pos (by norm_num)
  have oneb:1≤ b:=by
    apply Int.cast_one_le_of_pos
    rw[hb] at hrat
    contrapose! hrat
    rw[←rpow_intCast]
    apply rpow_le_one_of_one_le_of_nonpos
    norm_num
    norm_cast
  have above3:3≤(3:ℝ)^b:=by
    nth_rewrite 1[←rpow_one 3]
    rw[←rpow_intCast]
    apply rpow_le_rpow_of_exponent_le
    simp
    norm_cast
  have suboneabove2:2≤(3:ℝ)^(b)-1:=by norm_cast;linarith
--We need to bound the result of summation of geometric series by power of 3. This will give us the second equation of a and b.
--The first estimate aux1 is about the upper bound.
  have aux1:((3:ℝ) ^ a * (((3 ^ b) ^ 8 - 1) / (3 ^ b - 1)))<3^(a+(7*b+1)):=by
    rw[←rpow_intCast,←rpow_intCast,←rpow_intCast]
    simp only [ Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    rw[rpow_add]
    rw[mul_lt_mul_left]
    rw[←rpow_intCast] at suboneabove2
    rw[div_lt_iff]
    rw[mul_sub,←rpow_add,add_comm,←add_assoc]
    ring_nf
    rw[rpow_one_add',rpow_mul]
    have :(3:ℝ) ^ (1 + (b:ℝ) * 7)≤ (3^(b:ℝ))^8:=by
      rw[←rpow_natCast,←rpow_mul]
      apply rpow_le_rpow_of_exponent_le (by norm_num)
      norm_cast
      linarith;norm_num
    rw[lt_sub_iff_add_lt]
    calc
      -1 + ((3:ℝ) ^ (b:ℝ)) ^ 8 + (3:ℝ) ^ (1 + (b:ℝ)* 7)≤(3 ^ (b:ℝ)) ^ 8 + 3 ^ (1 + (b:ℝ) * 7):=by linarith
      _≤ (3 ^ (b:ℝ)) ^ 8+ (3 ^ (b:ℝ)) ^ 8:=by
        simp only [add_le_add_iff_left]
        apply this
      _<3*(3 ^ (b:ℝ)) ^ (8:ℝ):=by
        norm_cast
        ring_nf
        rw[mul_lt_mul_left]
        norm_num
        rw[←rpow_intCast,←rpow_natCast,←rpow_mul]
        apply rpow_pos_of_pos
        norm_num;norm_num
    all_goals
      try (linarith)
      try (norm_cast;linarith)
    apply rpow_pos_of_pos (by norm_num)
--Then we bound it below.
  have aux2:(3:ℝ)^(a+(7*b))<(3 ^ a * (((3 ^ b) ^ 8 - 1) / (3 ^ b - 1))):=by
    rw[←rpow_intCast,←rpow_intCast,←rpow_intCast,←rpow_natCast,←rpow_mul,Int.cast_add,rpow_add]
    rw[mul_lt_mul_left]
    rw[lt_div_iff]
    rw[mul_sub,←rpow_add,Int.cast_mul]
    norm_cast
    ring_nf
    rw[add_comm,sub_eq_add_neg]
    apply sub_lt_sub_left
    rw[←rpow_intCast]
    apply one_lt_rpow (by norm_num)
    all_goals
      norm_cast
      try simp
      try linarith
--We simplify h2 and h3 using aux1 and aux2 respectively.
  replace h2:56<logb 3 (3^(a+(7*b+1))):=by
    apply lt_of_le_of_lt h2
    apply logb_lt_logb (by norm_num)
    field_simp
    rw[←rpow_natCast]
    apply one_lt_rpow
    linarith;norm_num
    apply aux1
  replace h3:logb 3 (3^(a+(7*b)))<57:=by
    apply lt_of_le_of_lt' h3
    apply logb_lt_logb
    simp
    rw[←rpow_intCast]
    apply rpow_pos_of_pos;simp
    exact aux2
  rw[←rpow_intCast,logb_rpow] at h2 h3
  norm_cast at h2 h3
--We have two inequality for an integer a+7b. Because integers are discrete, we can determine it.
  have eq2:a+7*b=56:=by linarith
--We solve the equation to get a=21 and b=5.
  have hab:a=21∧b=5:=by
    constructor
    linarith
    linarith[eq2]
--Substitue the definition of x 14 and the values of a,b, we get our result 91.
  rw[xgeo,hab.1,hab.2]
  simp
  rw[←rpow_intCast,logb_rpow]
  norm_cast
  all_goals simp