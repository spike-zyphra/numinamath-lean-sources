import Mathlib

/- If $x$, $y$, and $z$ are positive integers such that
$6xyz+30xy+21xz+2yz+105x+10y+7z=812$, find $x+y+z$.-/
theorem algebra_20627 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 6*x*y*z+30*x*y+21*x*z+2*y*z+105*x+10*y+7*z=812) : x+y+z=10 := by
  -- to solve the problem, we need do some factorization
  -- add 35 to both sides may help, and we get following equation.
  have h1: (z+5)*(6*x*y+21*x+2*y+7) = 847 := by
    have: 847 = 812+35 := by norm_num
    rw [this, ← h]; ring
  -- continue factoring
  have h2: 6*x*y+21*x+2*y+7 = (3*x+1)*(2*y+7) := by ring
  -- so we have three parts multiply eq 847, each part divide 847
  -- however, 847 = 7x11x11, so these three parts must be 7 or 11
  let A := z+5
  have A_def: A = z+5 := rfl
  let B := 3*x+1
  have B_def: B = 3*x+1 := rfl
  let C := 2*y+7
  have C_def: C = 2*y+7 := rfl
  have Agt3: A > 3 := by
    rw [A_def]; linarith [hz]
  have Bgt3: B > 3 := by
    rw [B_def]; linarith [hx]
  have Cgt3: C > 3 := by
    rw [C_def]; linarith [hy]
  have eqabc: A*B*C = 847 := by
    rw [← h1, h2, ← A_def, ← B_def, ← C_def]; ring
  have eq7or11{a b c: ℕ}(ha: a>3)(hb: b>3)(hc: c>3)(heq: a*b*c=847):
    (a=7 ∨ a=11) ∧ (b=7 ∨ b=11) ∧ (c=7 ∨ c=11) := by
    have p7: Nat.Prime 7 := by norm_num
    have p11: Nat.Prime 11 := by norm_num
    have fac847: 847 = 7 * (11*11) := by norm_num
    have adv: a ∣ 7 * (11*11) := by
      rw [← fac847, ← heq]
      apply Nat.dvd_trans (Nat.dvd_mul_right a b) (Nat.dvd_mul_right _ _)
    have advor: 7 ∣ a ∨ a ∣ 11*11 := by
      apply Prime.left_dvd_or_dvd_right_of_dvd_mul (Nat.prime_iff.mp p7) adv
    have bdv: b ∣ 7 * (11*11) := by
      rw [← fac847, ← heq]
      apply Nat.dvd_trans (Nat.dvd_mul_left b a) (Nat.dvd_mul_right _ _)
    have bdvor: 7 ∣ b ∨ b ∣ 11*11 := by
      apply Prime.left_dvd_or_dvd_right_of_dvd_mul (Nat.prime_iff.mp p7) bdv
    have cdv: c ∣ 7 * (11*11) := by
      rw [← fac847, ← heq]
      apply Nat.dvd_mul_left
    have cdvor: 7 ∣ c ∨ c ∣ 11*11 := by
      apply Prime.left_dvd_or_dvd_right_of_dvd_mul (Nat.prime_iff.mp p7) cdv
    -- 11 is prime, so if some number divide 11x11, it can only be 1,11,121. and if that > 3,
    -- only solution is 11 and 121
    have dv11(m:ℕ)(mgt3: m > 3): m ∣ 11*11 → m = 11 ∨ m = 11*11 := by
      intro mdv
      have := Prime.left_dvd_or_dvd_right_of_dvd_mul (Nat.prime_iff.mp p11) mdv
      by_cases m11: m = 11
      · rw [m11]; simp
      · push_neg at m11
        rcases this with hh1 | hh2 <;> right
        · rcases hh1 with ⟨k,hk⟩
          have tt1: k ∣ 11 := by
            rw [hk] at mdv
            have: 0 < 11 := by norm_num
            apply Nat.dvd_of_mul_dvd_mul_left this mdv
          have tt2: k = 1 ∨ k = 11 := by
            exact (Nat.dvd_prime p11).mp tt1
          rcases tt2 with hkk | hkk
          · rw [hk, hkk] at m11; simp at m11
          · rw [hk, hkk]
        · have: m = 1 ∨ m = 11 := by
            exact (Nat.dvd_prime p11).mp hh2
          rcases this with tt1 | tt2
          · rw [tt1] at mgt3; norm_num at mgt3
          · rw [tt2] at m11; simp at m11
    have abceq{a' b' c' : ℕ}(ha': a' > 3)(hb': b' > 3)(hc': c' > 3)
      (advor': 7 ∣ a' ∨ a' ∣ 11*11)(heq': a'*b'*c'=847): a' = 7 ∨ a' = 11 := by
      rcases advor' with ha7' | ha11'
      · rcases ha7' with ⟨k,hk⟩
        have: k = 1 := by
          rw [hk, fac847] at heq'
          have hh1: b'*(k*c') = 11*11 := by
            linarith [heq']
          have beq': b' = 11 ∨ b' = 11*11 := by
            apply dv11 b' hb'
            rw [← hh1]
            exact Nat.dvd_mul_right b' (k * c')
          rcases beq' with b11 | b1111
          · have: k*c' = 11 := by
              rw [b11] at hh1; linarith [hh1]
            have ceq': c' = 1 ∨ c' = 11 := by
              have cdv11': c' ∣ 11 := by
                rw [← this]; exact Nat.dvd_mul_left c' k
              exact (Nat.dvd_prime p11).mp cdv11'
            rcases ceq' with hc1 | hc11
            · rw [hc1] at hc'; norm_num at hc'
            · rw [hc11] at this; linarith [this]
          · rw [b1111] at hh1; simp at hh1
            exfalso; omega
        rw [this] at hk; rw [hk]; simp
      · have hha := dv11 a' ha' ha11'
        rcases hha with a11 | a1111
        · rw [a11]; simp
        · have hbc: b'*c' = 7 := by
            rw [a1111, fac847] at heq'
            linarith [heq']
          have bdv7: b' ∣ 7 := by
            rw [← hbc]; exact Nat.dvd_mul_right b' c'
          rcases ((Nat.dvd_prime p7).mp bdv7) with b1 | b7
          · rw [b1] at hb'; norm_num at hb'
          · rw [b7] at hbc; simp at hbc
            rw [hbc] at hc'; norm_num at hc'
    have aeq: a = 7 ∨ a = 11 := by
      apply abceq ha hb hc advor heq
    have beq: b = 7 ∨ b = 11 := by
      have heq': b*c*a = 847 := by
        rw [← heq]; ring
      apply abceq hb hc ha bdvor heq'
    have ceq: c = 7 ∨ c = 11 := by
      have heq': c*a*b = 847 := by
        rw [← heq]; ring
      apply abceq hc ha hb cdvor heq'
    exact ⟨aeq, beq, ceq⟩
  -- from A,B,C = 7 or 11, we can solve the equations and find x,y,z
  have heq := eq7or11 Agt3 Bgt3 Cgt3 eqabc
  -- C = 2y+7, y > 0, so only solution is C = 11 and y = 2
  have yeq: y = 2 := by
    have: 2*y+7 = 7 ∨ 2*y+7 = 11 := by
      rw [← C_def]; exact heq.right.right
    omega
  -- B = 3x+1, 3x+1 cannot be 11, so B can only be 7, and x = 2
  have xeq: x = 2 := by
    have: 3*x+1 = 7 ∨ 3*x+1 = 11 := by
      rw [← B_def]; exact heq.right.left
    omega
  -- C=11 and B = 7, so A = 11, and z is determined.
  have zeq: z = 6 := by
    have hc: C = 11 := by
      rw [C_def, yeq]
    have hb: B = 7 := by
      rw [B_def, xeq]
    have ha: A = 11 := by
      rw [hb, hc] at eqabc
      linarith [eqabc]
    rw [A_def] at ha; linarith [ha]
  -- so x+y+z = 2+2+6 = 10
  rw [xeq, yeq, zeq]