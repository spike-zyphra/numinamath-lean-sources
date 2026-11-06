import Mathlib

-- Are there any positive integers $ m $ and $ n $ satisfying the equation $ m ^ 3 = 9 * n ^ 4 + 170 * n ^ 2 + 289 $ ?
theorem number_theory_604334 : ¬∃ m n : ℕ , m ^ 3 = 9 * n ^ 4 + 170 * n ^ 2 + 289 := by
  -- We will prove that the answer is no.
  by_contra! h
  rcases h with ⟨m, n, h⟩
  -- Note that $ m ^ 3 = 9 * n ^ 4 + 170 * n ^ 2 + 289 = (9 * n ^ 2 + 17)(n ^ 2 + 17) $
  have h' : m ^ 3 = (9 * n ^ 2 + 17) * (n ^ 2 + 17) := by rw [h] ;ring
  -- If $ n $ is odd then $ m $ is even, therefore $ 8 \| m ^ 3 $.
  by_cases hn : Odd n
  · have hm : Even m := by
      have : Even (m ^ 3) := by
        rw [h', Nat.even_mul]
        right
        apply Nat.even_add'.mpr
        rw [pow_two, Nat.odd_mul]
        simp [hn] ;exact Nat.odd_iff.mpr rfl
      exact (Nat.even_pow.mp this).1
    have hmd8 : 8 ∣ m ^ 3 := by
      have : 8 = 2 ^ 3 := rfl
      rw [this,Nat.pow_dvd_pow_iff]
      exact even_iff_two_dvd.mp hm ;simp
    -- However, $ 9 n^{4}+170 n^{2}+289 \equiv 9+170+289 \equiv 4(\bmod 8) $ which leads to a contradiction.
    have heqmod : (9 * n ^ 4 + 170 * n ^ 2 + 289) % 8 = 4 := by
      rcases Odd.exists_bit1 hn with ⟨k, hk⟩
      have : 2 * 2 = 4 := rfl
      rw [← this,pow_mul]
      simp [Nat.add_mod,pow_two,Nat.mul_mod]
      simp
      have : n * n % 8 = 1 := by
        have : n * n = 4 * k * (k + 1) + 1 := by rw [hk] ;ring
        rw [this,Nat.add_mod]
        have : 4 * k * (k + 1) % 8 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          have : 8 = 4 * 2 := rfl
          rw [this,mul_assoc]
          apply mul_dvd_mul (by rfl)
          rcases Nat.even_or_odd k with ⟨k',hkeven⟩  | ⟨k',hkodd⟩
          · rw [hkeven,← two_mul,mul_assoc]
            apply dvd_mul_of_dvd_left ;simp
          rw [hkodd,add_assoc,← two_mul,← mul_add,mul_comm]
          apply dvd_mul_of_dvd_left ;simp
        rw [this,zero_add]
      rw [Nat.add_mod,Nat.add_mod (n * n * (n * n))  (2 * (n * n)),Nat.mul_mod,Nat.mul_mod 2,this]
    rw [← h] at heqmod
    apply Nat.dvd_iff_mod_eq_zero.mp at hmd8
    rw [heqmod] at hmd8
    norm_num at hmd8
  --  If $ n $ is a multiple of 17 then so is $ m $ and hence 289 is a multiple of $ 17 ^ {3} $, which is absurd.
  by_cases hn' : 17 ∣ n
  have p17 : Prime 17 := by refine Nat.prime_iff.mp ?_ ;exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
  · have hm : 17 ∣ m := by
      have : 17 ∣ m ^ 3 := by
        rw [h']
        apply dvd_mul_of_dvd_right
        apply Nat.dvd_add
        rw [pow_two]
        apply dvd_mul_of_dvd_right
        exact hn'
        simp
      apply Prime.dvd_of_dvd_pow p17 this
    have hm3 : 17 ^ 3 ∣ m ^ 3 := pow_dvd_pow_of_dvd hm 3
    rw [h] at hm3
    rcases exists_eq_mul_right_of_dvd hn' with ⟨k,hk⟩
    have : 17 ^ 3 ∣ 9 * n ^ 4 + 170 * n ^ 2 := by
      rw [hk]
      ring_nf
      apply Nat.dvd_add
      · apply dvd_mul_of_dvd_right ;norm_num
      apply dvd_mul_of_dvd_right ;norm_num
    have : 17 ^ 3 ∣ 289 := (Nat.dvd_add_iff_right this).mpr hm3
    norm_num at this
  -- For $n$ even and not multiple of 17, since $ \operatorname{gcd}\left(9 n^{2}+17, n^{2}+17\right) \mid 9\left(n^{2}+17\right)-\left(9 n^{2}+17\right)=2^{3} \cdot 17 $ this gcd must be 1.
  have hgcd_dvd : Nat.gcd (9 * n ^ 2 + 17) (n ^ 2 + 17) ∣ 2 ^ 3 * 17 := by
    have : 2 ^ 3 * 17 + (9 * n ^ 2 + 17) = 9 * (n ^ 2 + 17) := by ring
    rcases Nat.eq_sub_of_add_eq this with this'
    rw [this']
    apply Nat.dvd_sub
    simp [← this]
    apply dvd_mul_of_dvd_right ;apply Nat.gcd_dvd_right ;apply Nat.gcd_dvd_left
  rcases Nat.dvd_mul.mp hgcd_dvd with ⟨x,y,hx,hy,hxy⟩
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hx with ⟨k,hk1,hk2⟩
  simp at hn
  by_cases hk3 : k > 0
  · rcases Nat.exists_eq_add_one.mpr hk3 with ⟨k',hk'⟩
    have : 2 ∣ x := by rw [hk2,hk',pow_add,pow_one] ;apply dvd_mul_of_dvd_right ;norm_num
    have : 2 ∣ (9 * n ^ 2 + 17).gcd (n ^ 2 + 17) := by rw [← hxy] ;apply dvd_mul_of_dvd_left ;exact this
    apply Nat.dvd_gcd_iff.mp at this
    rcases this.2 with this'
    have : 2 ∣ n ^ 2 := by rw [pow_two] ;apply dvd_mul_of_dvd_left ;exact even_iff_two_dvd.mp hn
    apply (Nat.dvd_add_iff_right this).mpr at this'
    norm_num at this'
  simp at hk3
  rw [← pow_one 17] at hy
  rcases (Nat.dvd_prime_pow (by norm_num)).mp hy with ⟨k',hk'1,hk'2⟩
  by_cases hk'3 : k' > 0
  · rcases Nat.exists_eq_add_one.mpr hk'3 with ⟨k'',hk''⟩
    have : 17 ∣ y := by rw [hk'2,hk'',pow_add,pow_one] ;apply dvd_mul_of_dvd_right ;norm_num
    have : 17 ∣ (9 * n ^ 2 + 17).gcd (n ^ 2 + 17) := by rw [← hxy] ;apply dvd_mul_of_dvd_right ;exact this
    apply Nat.dvd_gcd_iff.mp at this
    rcases this.2 with this'
    apply (Nat.dvd_add_iff_left (by norm_num)).mpr at this'
    apply Nat.Prime.dvd_of_dvd_pow (by norm_num) at this'
    exact hn' this'
  simp at hk'3
  rw [hk2,hk'2,hk3,hk'3,pow_zero,pow_zero,mul_one] at hxy
  -- Therefore $ n^{2}+17=a^{3} $ for an odd $ a $,
  have ha : ∃ a , n ^ 2 + 17 = a ^ 3 := by
    rw [mul_comm] at h'
    have : IsUnit (gcd (n ^ 2 + 17) (9 * n ^ 2 + 17)) := by simp [hxy,Nat.gcd_comm] ;rfl
    apply exists_eq_pow_of_mul_eq_pow this h'.symm
  rcases ha with ⟨a,ha⟩
  have ha' : Odd a := by
    have : Odd (n ^ 2 + 17) := by
      apply Even.add_odd
      · apply Nat.even_pow.mpr ;simp [hn]
      exact Nat.odd_iff.mpr rfl
    rw [ha] at this
    exact Nat.Odd.of_mul_right this
  -- so $ n^{2}+25=(a+2)\left(a^{2}-2 a+4\right) $
  have : 2 ^ 3 < a ^ 3 := by rw [← ha] ;simp
  have t : 2 < a := by exact lt_of_pow_lt_pow_left' 3 this
  have ha'' : n ^ 2 + 25 = (a + 2) * (a ^ 2 - 2 * a + 4) := by
    have : 25 = 17 + 8 := rfl
    rw [this,← add_assoc,ha,mul_add,Nat.mul_sub,add_mul,add_mul,pow_two,Nat.sub_add_eq]
    rw [mul_comm a (2*a),mul_assoc,Nat.add_sub_cancel,add_mul,← add_assoc,← mul_assoc 2]
    simp
    rw [mul_comm 4 a,Nat.sub_add_cancel,pow_three]
    have : 2 * 2 < a * a := by exact Nat.mul_lt_mul_of_lt_of_lt t t
    apply Nat.mul_le_mul ;rfl ;linarith
  -- For $a \equiv 1(\bmod 4)$ we have $a+2 \equiv 3(\bmod 4)$,while for $a \equiv 3(\bmod 4)$ we have $a^{2}-2 a+4 \equiv 3$ $(\bmod 4)$.
  -- Thus $(a+2)\left(a^{2}-2 a+4\right)$ has a prime divisor of type $4 \ell+3$.
  have hp : ∃ p , Prime p ∧ p % 4 = 3 ∧ p ∣ n ^ 2 + 25 := by
    by_contra! h
    rw [ha''] at h
    rcases ha' with ⟨k,hk⟩
    rcases Nat.even_or_odd k with ⟨k',hkeven⟩  | ⟨k',hkodd⟩
    · have tt : (a + 2) % 4 = 3 := by simp [hk,hkeven,← two_mul,← mul_assoc,add_assoc,Nat.mul_add_mod]
      have : ∀ p ∈ (Nat.primeFactorsList (a + 2)), p % 4 = 1 := by
        intro p hp
        rcases Nat.mem_primeFactorsList'.mp hp with ⟨hp1,hp2,hp3⟩
        have : Odd p := by apply Odd.of_dvd_nat ?_ hp2 ;apply Nat.odd_add.mpr ;simp [hk]
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp this) with h'|h'
        exact h'
        specialize h p (Nat.prime_iff.mp hp1) h'
        have : ¬p ∣ (a + 2) := by contrapose! h ;exact Dvd.dvd.mul_right hp2 (a ^ 2 - 2 * a + 4)
        exact False.elim (this hp2)
      have this' : (Nat.primeFactorsList (a + 2)).prod % 4 = 1 := by
        rw [List.prod_nat_mod]
        have : (List.map (fun x ↦ x % 4) (a + 2).primeFactorsList).prod = 1 := by
          apply List.prod_eq_one ;simp
          intro p x hx1 hx2 hx3
          rw [← hx3]
          apply this ;simp [hx1,hx2]
        rw [this]
      rw [Nat.prod_primeFactorsList (by simp) ] at this'
      rw [tt] at this'
      norm_num at this'
    have tt : (a ^ 2 - 2 * a + 4) % 4 = 3 := by
      have : a % 4 = 3 := by rw [hk,hkodd,mul_add,← mul_assoc,add_assoc] ;simp [Nat.mul_add_mod]
      rw [pow_two,Nat.add_mod,← Nat.sub_mul,Nat.mul_mod,this]
      have : (a - 2) % 4 = 1 := by
        refine Nat.mod_eq_of_modEq ?_ (by simp)
        refine Nat.ModEq.add_right_cancel' 2 ?_
        rw [Nat.sub_add_cancel]
        simp ;exact this ;linarith
      rw [this]
    have : ∀ p ∈ (Nat.primeFactorsList (a ^ 2 - 2 * a + 4)), p % 4 = 1 := by
      intro p hp
      rcases Nat.mem_primeFactorsList'.mp hp with ⟨hp1,hp2,hp3⟩
      have : Odd p := by
        apply Odd.of_dvd_nat ?_ hp2
        apply Nat.odd_add.mpr
        constructor
        · intro h1 ;exact Nat.even_iff.mpr rfl
        intro h1
        apply Nat.Odd.sub_even
        · rw [pow_two] ;apply Nat.mul_le_mul ;linarith ;rfl
        · apply Odd.pow ;simp [hk]
        simp
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp this) with h'|h'
      exact h'
      specialize h p (Nat.prime_iff.mp hp1) h'
      have : ¬p ∣ (a ^ 2 - 2 * a + 4) := by contrapose! h ;exact Dvd.dvd.mul_left hp2 (a + 2)
      exact False.elim (this hp2)
    have this' : (Nat.primeFactorsList (a ^ 2 - 2 * a + 4)).prod % 4 = 1 := by
      rw [List.prod_nat_mod]
      have : (List.map (fun x ↦ x % 4) (a ^ 2 - 2 * a + 4).primeFactorsList).prod = 1 := by
        apply List.prod_eq_one ;simp
        intro p x hx1 hx2 hx3
        rw [← hx3]
        apply this ;simp [hx1,hx2]
      rw [this]
    rw [Nat.prod_primeFactorsList (by simp) ] at this'
    rw [tt] at this'
    norm_num at this'
  rcases hp with ⟨p,hp1,hp2,hp3⟩
  -- As it divides $n^{2}+25$, it has to divide $n$ and 5, which is absurd.
  have hdvd : p ∣ 5 := by
    by_contra! h
    have : n ^ 2 + ((5 ^ 2) : ZMod p) = 0 := by
      have : ((5 ^ 2) : ZMod p) = ↑(5:ℕ)^2 := by simp
      rw [this,← Nat.cast_pow,← Nat.cast_pow,← Nat.cast_add]
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd (n ^ 2 + 5 ^ 2) p).mpr
      simp ;exact hp3
    have : n ^ 2 = -((5 ^ 2) : ZMod p) := by exact Eq.symm (neg_eq_of_add_eq_zero_left this)
    have : p % 4 ≠ 3 := by
      have fact : Fact (Nat.Prime p) := by refine { out := ?_ } ;exact Prime.nat_prime hp1
      apply ZMod.mod_four_ne_three_of_sq_eq_neg_sq' ?_ this
      by_contra!
      have this' : (5 : ZMod p) = ↑(5:ℕ) := by simp
      rw [this'] at this
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd 5 p).mp at this
      exact h this
    exact this hp2
  apply (Nat.dvd_prime Nat.prime_five).mp at hdvd
  rcases hdvd with h2 | h2
  · rw [h2] at hp2 ;norm_num at hp2
  rw [h2] at hp2 ;norm_num at hp2