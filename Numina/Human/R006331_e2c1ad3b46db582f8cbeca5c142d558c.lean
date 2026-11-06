import Mathlib
set_option maxRecDepth 500000
set_option maxHeartbeats 500000

/-
Let c ≥ 0 be an integer, and a,b > 0 be integers satisfying
  c * a^2 + a = (c + 1) * b^2 + b.
We show that a - b is a perfect square (in ℤ).
-/

theorem a_minus_b_eq_perfect_square {c : ℤ}
  (a b : ℤ)  (hab : b < a)
  (heq : c * a ^ 2 + a = (c + 1) * b ^ 2 + b) :
  IsSquare (a - b) := by

  -- Step 1: Rewrite the equation to show c*(a²-b²) + (a-b) = b²
  have heq' : c * (a ^ 2 - b ^ 2) + (a - b) = b ^ 2 := by
    calc
      c * (a ^ 2 - b ^ 2) + (a - b)
          = c * a ^ 2 - c * b ^ 2 + a - b := by ring
      _ = (c * a ^ 2 + a) - (c * b ^ 2 + b)       := by ring
      _ = (c + 1) * b ^ 2 + b - (c * b ^ 2 + b)   := by omega
      _ = b ^ 2                                  := by ring

  -- Step 2: Factorize to get (a-b)*(c*(a+b)+1) = b²
  have fact : (a - b) * (c * (a + b) + 1) = b ^ 2 := by
    calc
      (a - b) * (c * (a + b) + 1)
          = c * (a - b) * (a + b) + (a - b)       := by ring
      _ = c * (a ^ 2 - b ^ 2) + (a - b)           := by
        refine (Int.add_left_inj (a - b)).mpr ?_
        linarith
      _ = b ^ 2                                  := by simpa using heq'

  -- Step 3: Prove that (a-b) and (c*(a+b)+1) are coprime
  have coprime : ∀ d, a - b ≡ 0 [ZMOD d] → (c*(a + b) + 1) ≡ 0 [ZMOD d] → d = 1 ∨ d = -1 := by
    intro d h1 h2
    -- Convert modular equivalences to divisibility
    have hd1 : d ∣ a - b := Int.modEq_zero_iff_dvd.1 h1
    have hd2 : d ∣ c * (a + b) + 1 := Int.modEq_zero_iff_dvd.1 h2
    -- From the factored equation, d must divide b²
    have hb2 : d ∣ b ^ 2 := by rw [← fact]; exact dvd_mul_of_dvd_left hd1 _
    -- Since a ≡ b mod d, we can substitute in the second term
    have hb2_mod : b ^ 2 ≡ 0 [ZMOD d] := Int.modEq_zero_iff_dvd.2 hb2
    have hab_mod : a ≡ b [ZMOD d] := by
      rw [Int.modEq_iff_dvd] at h1 ⊢
      aesop
    -- Calculate c(a+b)+1 ≡ 2cb+1 (mod d)
    have hsum : a + b ≡ b + b [ZMOD d] := Int.ModEq.add_right _ hab_mod
    have hsum': a + b ≡ 2 * b [ZMOD d] := by
      rw [two_mul]
      exact hsum
    have h_mul : c * (a + b) ≡ c * (2 * b) [ZMOD d] := Int.ModEq.mul_left c hsum'
    have h2cb : c * (a + b) + 1 ≡ c * (2 * b) + 1 [ZMOD d] := by
      exact Int.ModEq.add_right 1 h_mul
    -- Simplify c*(a+b)+1 ≡ 2cb+1 ≡ 0 mod d
    have h2cb_zero : 2 * c * b + 1 ≡ 0 [ZMOD d] := by
      rw [← mul_assoc, mul_comm c 2] at h2cb
      simp only [Int.ModEq] at h2cb
      simp only [← Int.modEq_zero_iff_dvd] at hd2
      exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h2)) h2cb)
    -- Square the second congruence: (2cb+1)² ≡ 0 mod d
    have hsq : (2 * c * b + 1) ^ 2 ≡ 0 [ZMOD d] := by
      rw [Int.ModEq]
      simp
      refine Dvd.dvd.pow ?_ ?_
      exact Int.dvd_of_emod_eq_zero h2cb_zero
      norm_num
    have h_expand : (2 * c * b + 1) ^ 2 = 4 * c ^ 2 * b ^ 2 + 4 * c * b + 1 := by ring
    rw [h_expand] at hsq
    -- Expand the square and substitute b² ≡ 0 mod d
    have h4b2 : 4 * c ^ 2 * b ^ 2 ≡ 0 [ZMOD d] := by
      refine Dvd.dvd.modEq_zero_int ?_
      exact Dvd.dvd.mul_left hb2 (4 * c ^ 2)
    have h4cb : 4 * c * b ≡ 0 [ZMOD d] := by
      have t1 : (b ^ 2) * 4≡ 0 *4[ZMOD d] := by exact Int.ModEq.mul hb2_mod rfl
      have t3 : (b ^ 2) * 4*c≡ 0 *c [ZMOD d] := by exact Int.ModEq.mul t1 rfl
      have t4 : (b ^ 2) * 4*c≡ 0 [ZMOD d] := by aesop
      have t5 : (2 * c * b + 1)*2 ≡ 0*2 [ZMOD d] := by exact Int.ModEq.mul h2cb_zero rfl
      have t7 : (2 * c * b + 1)*2*b ≡ 0*b [ZMOD d] := by exact Int.ModEq.mul t5 rfl
      have t8 : (2 * c * b + 1)*2*b ≡ 0 [ZMOD d] := by aesop
      have t9 : (2 * c * b + 1)*(2*b) ≡ 0 [ZMOD d] := by rw [mul_assoc] at t8;exact t8
      have t10':2 * c * b * 2 * b=4*c*b*b:=by ring
      have t10: 4*c*b*b+2*b≡0 [ZMOD d] := by rw [add_mul,one_mul,← mul_assoc] at t9;rw [t10'] at t9;exact t9
      have t4':4 * c * b * b=b^2*4*c:=by ring
      have t4'':4 * c * b * b≡0[ZMOD d]:=by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm t4)) (congrFun (congrArg HMod.hMod (id (Eq.symm t4'))) d))
      have t11':2*b=4*c*b*b+2*b-4*c*b*b:=by ring
      have t11:(4*c*b*b+2*b)-(4*c*b*b)≡0-0[ZMOD d]:=by exact Int.ModEq.symm (Int.ModEq.sub (id (Int.ModEq.symm t10)) (id (Int.ModEq.symm t4'')))
      have t11':(4*c*b*b+2*b)-(4*c*b*b)≡0[ZMOD d]:=by exact t11
      have t12:(4*c*b*b+2*b)-(4*c*b*b)=2*b:=by ring
      have t13:2*b≡0[ZMOD d]:=by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm t11)) (congrFun (congrArg HMod.hMod t12) d))
      have t14:4*c*b=2*b*(2*c):=by ring
      have t14':2*b*(2*c)≡0*(2*c)[ZMOD d]:=by exact Int.ModEq.mul t13 rfl
      have t14'':0*(2*c)=0:=by ring
      have t14''':2*b*(2*c)≡0[ZMOD d]:=by exact Int.ModEq.symm (Int.ModEq.trans (congrFun (congrArg HMod.hMod (id (Eq.symm t14''))) d) (id (Int.ModEq.symm t14')))
      have t15:2*b*(2*c)=4*c*b:=by ring
      exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm t14''')) (congrFun (congrArg HMod.hMod t15) d))
    have h_sum : 4 * c ^ 2 * b ^ 2 + 4 * c * b ≡ 0 [ZMOD d] := Int.ModEq.add h4b2 h4cb
    -- Combining results gives 1 ≡ 0 mod d, so d must divide 1
    have h1 : 1 ≡ 0 [ZMOD d] := by
      exact Int.ModEq.symm (Int.ModEq.add_left_cancel (id (Int.ModEq.symm h_sum)) (id (Int.ModEq.symm hsq)))
    -- Find that d | 1
    rw [Int.modEq_zero_iff_dvd] at h1
    have h2: |d|∣1:=by exact (abs_dvd d 1).mpr h1
    have h3: |d| > 0:=by
      by_contra
      aesop
    have h4: |d|≤ 1:= by refine Int.le_of_dvd ?_ h2;simp
    refine abs_eq_abs.mp ?_
    simp
    omega

  -- Step 4: Prove gcd(a-b, c*(a+b)+1) = 1 using coprimality
  have gcd_eq_one : Int.gcd (a - b) (c * (a + b) + 1) = 1 := by
    let g := Int.gcd (a - b) (c * (a + b) + 1)
    have hg1 : (g : ℤ) ∣ a - b :=by exact Int.gcd_dvd_left
    have hg2 : (g : ℤ) ∣ c * (a + b) + 1 := Int.gcd_dvd_right
    -- Apply the lemma from the coprime relationship
    have h_coprime := coprime g (Int.modEq_zero_iff_dvd.mpr hg1) (Int.modEq_zero_iff_dvd.mpr hg2)
    have g_nonneg : (0 : ℤ) ≤ g := by omega
    -- Now cases to h_coprime
    cases h_coprime with
    | inl h1 =>
        omega
    | inr h_neg =>
        rw [h_neg] at g_nonneg
        linarith

  -- Step 5: The product is a square (b²) and factors are coprime ⇒ each is a square
  have sqab : IsSquare (a - b) := by
    have pos : a-b>0 := by exact Int.sub_pos_of_lt hab
    have t1 : ∃ x , (a - b) = x ^ 2 ∨ (a-b) = -x^2 := by
      exact Int.sq_of_gcd_eq_one gcd_eq_one fact
    refine (isSquare_iff_exists_sq (a - b)).mpr ?_
    rcases t1 with ⟨t11,t12|t12⟩
    exact ⟨t11,t12⟩
    have neg : a-b<=0 := by
      rw [t12]
      exact neg_nonpos.mpr (sq_nonneg t11)
    linarith
  exact sqab
