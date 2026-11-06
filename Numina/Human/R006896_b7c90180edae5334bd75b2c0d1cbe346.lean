import Mathlib

/-
Theorem: For prime p dividing n⁴ - n² + 1, p ≡ 1 mod 12
Given: Natural numbers n and prime p such that p divides n⁴ - n² + 1
Prove: There exists natural number k such that p = 12k + 1
-/
theorem imotrain_quad_4(n p:ℕ)(hp:Nat.Prime p)[Fact p.Prime](hn:p∣ (n^4-n^2+1)): ∃ k,p=12*k+1:=by
  -- Case when n ≤ 1: trivial since n⁴ - n² + 1 = 1
  have pp:p>1:=by exact Nat.Prime.one_lt hp
  by_cases o:n≤1
  have h1:n^4-n^2+1=1:=by
    have t:n=0∨n=1:=by omega
    cases t
    case inl h=>simp[h]
    case inr h=>simp[h]
  have h2:p=1:=by
    rw[h1] at hn
    exact Nat.eq_one_of_dvd_one hn
  use 0
  -- Main case: n > 1
  push_neg at o

  -- Preliminary work: Show n ≢ 0 mod p
  have t:(n:ZMod p)≠(0:ZMod p):=by
    by_contra h
    have t1:p∣ n:=by exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp h
    have t2:p∣ n^4-n^2:=by refine Nat.dvd_sub' ?_ ?_;all_goals refine Dvd.dvd.pow t1 ?_ ;linarith
    have t3:p∣ 1:=by exact (Nat.dvd_add_iff_right t2).mpr hn
    aesop

  -- Prove p > 2 (since p=2 leads to contradiction)
  have t_1:p>2:=by
    by_contra h
    have t1:p=2:=by omega
    rw[t1] at hn
    mod_cases n%2
    have t2: 2∣ n:=by exact Nat.dvd_of_mod_eq_zero H
    have t3:2∣ n^4-n^2:=by refine Nat.dvd_sub' ?_ ?_;all_goals refine Dvd.dvd.pow t2 ?_;linarith
    have t4:2∣ 1:=by exact (Nat.dvd_add_iff_right t3).mpr hn
    aesop
    have t2:n^2≡ 1^2[MOD 2]:=by exact Nat.ModEq.pow 2 H
    have t3:n^4≡ 1^4[MOD 2]:=by exact Nat.ModEq.pow 4 H
    simp_all
    have t4:2∣ n^2-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t2));refine Nat.one_le_pow 2 n ?_;linarith
    have t5:2∣ n^4-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t3));refine Nat.one_le_pow 4 n ?_;linarith
    have t6:2∣ (n^4-1)-(n^2-1):=by exact Nat.dvd_sub' t5 t4
    have t7: (n^4-1)-(n^2-1)=n^4-n^2:=by refine Nat.sub_sub_sub_cancel_right ?_;refine Nat.one_le_pow 2 n ?_;linarith
    omega

  -- Prove p ≠ 3 (case analysis mod 3)
  have t_2:p≠3:=by
    by_contra h
    rw[h] at hn
    mod_cases n%3
    have t1:n^2≡0^2[MOD 3]:=by exact Nat.ModEq.pow 2 H
    have t2:n^4≡0^4[MOD 3]:=by exact Nat.ModEq.pow 4 H
    have t3:3∣ n^2-0:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t1));exact sq_nonneg n
    have t4:3∣ n^4-0:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t2));exact Nat.zero_le (n ^ 4)
    omega
    have t1:n^2≡1^2[MOD 3]:=by exact Nat.ModEq.pow 2 H
    have t2:n^4≡1^4[MOD 3]:=by exact Nat.ModEq.pow 4 H
    have t3:3∣ n^2-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t1));refine Nat.one_le_pow 2 n ?_;linarith
    have t4:3∣ n^4-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t2));refine Nat.one_le_pow 4 n ?_;linarith
    omega
    have t1:n^2≡2^2[MOD 3]:=by exact Nat.ModEq.pow 2 H
    have t2:n^4≡2^4[MOD 3]:=by exact Nat.ModEq.pow 4 H
    have t3:3∣ n^2-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t1));refine Nat.one_le_pow 2 n ?_;linarith
    have t4:3∣ n^4-1:=by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm t2));refine Nat.one_le_pow 4 n ?_;linarith
    omega

  -- Prove p is odd (since p > 2)
  have t_3: p%2=1:=by
    refine Nat.odd_iff.mp ?_
    refine Nat.Prime.odd_of_ne_two hp ?_
    exact Ne.symm (Nat.ne_of_lt t_1)

  -- Algebraic identities for n⁴ - n² + 1
  have h1:n^4-n^2+1=((n^2)-1)^2+n^2:=by
    have t1:∃a>0,n=1+a:=by exact lt_iff_exists_add.mp o
    obtain⟨a,ha,pa⟩:=t1
    simp[pa,add_sq]
    have t2:1 + 2 * a + a ^ 2 - 1= 2 * a + a ^ 2 :=by omega
    simp[t2]
    ring_nf
    omega
  have h_1:(n^2)^2=n^4:=by ring
  have h_2:n^4≥n^2:=by refine Nat.pow_le_pow_of_le o ?_;linarith
  have h2':n^4-n^2+1=(n^2+1)^2-3*n^2:=by simp[add_sq];omega

  -- First step: Prove p ≡ 1 mod 4 using sum of squares
  let x:=(n^2)-1
  let a:=(x)^2+n^2
  have h2:a=(0:ZMod p):=by
    refine (ZMod.natCast_zmod_eq_zero_iff_dvd a p).mpr ?_
    rw[h1] at hn
    exact hn
  simp[a] at h2
  have t1:(x)^2=(-n^2:ZMod p):=by exact Eq.symm (neg_eq_of_add_eq_zero_left h2)
  have t2: p % 4 ≠ 3 :=by exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' t t1
  have t3:p%4=1:=by
    have t4:p%4=1∨ p%4=3:=by exact Nat.odd_mod_four_iff.mp t_3
    simp at t4
    tauto

  -- Second step: Prove p ≡ 1 mod 3 using quadratic reciprocity
  let b:=n^2+1
  have h2:b^2≡3*n^2 [MOD p]:=by
    refine Nat.ModEq.symm ((fun {n a b} h => (Nat.modEq_iff_dvd' h).mpr) ?_ ?_)
    simp[b]
    omega
    aesop
  have t1:(b)^2=((3:ℤ)*n^2:ZMod p):=by
    norm_cast;
    refine (ZMod.natCast_eq_natCast_iff (b ^ 2) (3 * n ^ 2) p).mpr ?_
    tauto
  have t2:(b:ZMod p)^2-(3:ℤ)*n^2=(0:ZMod p):=by exact sub_eq_zero_of_eq t1
  have h4: legendreSym p 3 = 1:=by
    refine legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero ?_ t t2;
    by_contra h
    have y:(p:ℤ )∣(3:ℤ ):=by exact (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp h
    have y1:p∣ 3:=by exact Int.ofNat_dvd.mp y
    have y2:p=3∨ p=1:=by refine Or.symm ((fun {p m} pp => (Nat.dvd_prime pp).mp) ?_ y1);trivial
    aesop
  have h5: legendreSym 3 p = legendreSym p 3:=by
    apply legendreSym.quadratic_reciprocity_one_mod_four
    tauto
    trivial

  -- Final step: Case analysis modulo 3
  mod_cases p%3
  -- Case p ≡ 0 mod 3 (contradiction since p ≠ 3)
  have t1:3=p:=by
    have t2:3∣p:=by exact Nat.dvd_of_mod_eq_zero H
    have t3:3=1∨3=p:=by exact (Nat.dvd_prime hp).mp t2
    simp at t3
    tauto
  aesop

  -- Case p ≡ 1 mod 3 (combine with p ≡ 1 mod 4)
  have t1:∃s,p-1=4*s:=by refine dvd_def.mp ?_;refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm t3));linarith
  obtain⟨s,hs⟩:=t1
  have t2:∃u,p-1=3*u:=by refine dvd_def.mp ?_;refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm H));linarith
  obtain⟨u,hu⟩:=t2
  have t3:p=12*(u-s)+1:=by omega
  use (u-s)

  -- Case p ≡ 2 mod 3 (contradiction with quadratic reciprocity)
  rw[h4] at h5
  have t1:legendreSym 3 p = (p : ZMod 3) ^ (3 / 2) :=by apply legendreSym.eq_pow
  simp[h5] at t1
  by_contra
  have t8:∃s',p-2=3*s':=by refine exists_eq_mul_right_of_dvd ?_;exact (Nat.modEq_iff_dvd' pp).mp (id (Nat.ModEq.symm H))
  obtain⟨s',hs'⟩:=t8
  have t9:p=3*s'+2:=by refine (Nat.sub_eq_iff_eq_add ?_).mp hs';linarith
  have t10:(p:ZMod 3)=3*s'+2:=by norm_cast;exact congrArg Nat.cast t9
  have t11:3*s'=(0:ZMod 3):=by exact mul_eq_zero_comm.mp rfl
  simp[t10,t11] at t1
  tauto
