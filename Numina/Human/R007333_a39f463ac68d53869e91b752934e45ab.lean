import Mathlib

open Polynomial
/-The equation z^6+z^3+1=0 has complex roots with argument θ between 90∘ and 180∘ in the complex plane. Determine the degree measure of θ.-/

theorem AIME_Algebra_94679 (z : ℂ) (hz : z^6 + z^3 + 1 = 0)  (θ : ℝ)
(hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi ∧ z.arg = θ) :
θ * 180 / Real.pi = 160 := by 
--We first prove that z is a primitive root of unity of degree 9.
  rcases hθ with ⟨h1,h2⟩
--First, we prove that X^6+X^3+1 is the 9-th cyclotomic polynomial.
  have cycpoly:(Polynomial.cyclotomic 9 ℂ)=X^6+X^3+1:=by
    have :9=3^2:=rfl
    rw[this]
    symm
--We prove that the product of this polynomial with the cyclotomic polynomial of proper divisors of 9 is X^9-1.
    rw[Polynomial.eq_cyclotomic_iff]
--Proper divisors of 9 are 1 and 3.
    have :(3 ^ 2).properDivisors={1,3}:=by decide
    rw[this]
    simp only [Nat.reducePow, Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,Finset.prod_insert, cyclotomic_one, Finset.prod_singleton, cyclotomic_three]
    ring
    norm_num
--Now because z is a root of the cyclotomic polynomial, it is a primitive root.
  have zuni:IsPrimitiveRoot z 9:=by
    rw[←Polynomial.isRoot_cyclotomic_iff]
    rw[cycpoly]
    simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
    rw[hz]
--We get explicit information about theta.
  have zarg:=IsPrimitiveRoot.arg zuni (by norm_num)
  rcases zarg with ⟨i,hi,iprime,ilt⟩
--We use the condition on theta to bound i.
  rw[hi] at h2
  rw[←h2] at h1 ⊢
  simp only [Nat.cast_ofNat, Set.mem_Ioo] at h1
  ring_nf at h1
  nth_rewrite 4[←mul_one Real.pi] at h1
  rw[mul_assoc] at h1
  rw[mul_lt_mul_left,mul_lt_mul_left] at h1
  rcases h1 with ⟨ha,hb⟩
  swap
  exact Real.pi_pos
  swap
  exact Real.pi_pos
--Now we prove that i=4, then theta must be 8*π/9. First, i is nonnegative.
  have ipos:i=i.natAbs:=by
    apply Int.eq_natAbs_of_zero_le
    rw[←div_lt_iff] at ha
    norm_num at ha
    rw[←(@Int.cast_le Real)]
    apply le_of_lt
    apply lt_trans' ha
    norm_num
    norm_num
  rw[ipos]
  interval_cases i.natAbs
--Since 1/2< i*(2/9)<1, we have i=3 or i=4
  all_goals
    revert ha hb
    rw[ipos]
    norm_num
--Because z is a primitive root, i=3 is impossible
  rw[ipos] at iprime
  contrapose! iprime
  norm_num
--We prove that i=4 is correct.
  field_simp
  rw[mul_comm,←mul_assoc,←mul_assoc,←mul_assoc]
  norm_num