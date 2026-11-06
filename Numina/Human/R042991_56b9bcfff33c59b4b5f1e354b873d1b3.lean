import Mathlib

/- If $a,b,c$ are positive integers less than $13$ such that \begin{align*}
2ab+bc+ca&\equiv 0\pmod{13}\\
ab+2bc+ca&\equiv 6abc\pmod{13}\\
ab+bc+2ca&\equiv 8abc\pmod {13}
\end{align*}then determine the remainder when $a+b+c$ is divided by $13$. -/
theorem number_theory_23074 (a b c : ℤ) (ha : 0 < a ∧ a < 13) (hb : 0 < b ∧ b < 13) (hc : 0 < c ∧ c < 13)
    (h1 : 2*a*b+b*c+c*a ≡ 0 [ZMOD 13]) (h2 : a*b+2*b*c+c*a ≡ 6*a*b*c [ZMOD 13]) (h3 : a*b+b*c+2*c*a ≡ 8*a*b*c [ZMOD 13]) :
    a+b+c ≡ 5 [ZMOD 13] := by
  have an: ↑a.toNat = a := Int.toNat_of_nonneg (le_of_lt ha.left)
  have bn: ↑b.toNat = b := Int.toNat_of_nonneg (le_of_lt hb.left)
  have cn: ↑c.toNat = c := Int.toNat_of_nonneg (le_of_lt hc.left)
  -- since a,b,c < 13 and 13 is prime,  a,b,c are invertible modulo 13.
  have p13: Nat.Prime 13 := by norm_num
  have inv_m(m:ℤ)(hm: 0 < m ∧ m < 13)(mn: ↑m.toNat = m):
    ∃x:ℤ, x*m ≡ 1 [ZMOD 13] := by
    have hh1: Nat.Coprime m.toNat 13 := by
      rw [Nat.coprime_comm]
      rw [Nat.Prime.coprime_iff_not_dvd p13]
      have: m.toNat < 13 := by
        have: (m.toNat:ℤ) < ↑(13:ℕ) := by
          rw [mn]; simp; exact hm.right
        exact Int.ofNat_lt.mp this
      apply Nat.not_dvd_of_pos_of_lt
      · have: 0 < (m.toNat:ℤ) := by
          rw [mn]; apply hm.left
        exact Int.ofNat_pos.mp this
      · exact this
    have hh2 := Int.mod_coprime hh1
    simp [le_of_lt hm.left] at hh2
    rcases hh2 with ⟨d,hd⟩
    use d
    rwa [mul_comm] at hd
  -- let x be a⁻¹, and y b⁻¹, z c⁻¹.
  rcases (inv_m a ha an) with ⟨x,hx⟩
  rcases (inv_m b hb bn) with ⟨y,hy⟩
  rcases (inv_m c hc cn) with ⟨z,hz⟩
  -- notice that ab xyz = z, bc xyz = x, and ca xyz = y.
  have h4: a*b*(x*y*z) ≡ z [ZMOD 13] := by
    have hh1: a*b*(x*y*z) = (x*a)*(y*b)*z := by ring
    have hh2: (x*a)*(y*b) ≡ 1 [ZMOD 13] := by
      rw [← mul_one 1]
      exact Int.ModEq.mul hx hy
    nth_rw 2 [← mul_one z]
    rw [hh1, mul_comm z 1]
    exact Int.ModEq.mul hh2 rfl
  have h5: b*c*(x*y*z) ≡ x [ZMOD 13] := by
    have hh1: b*c*(x*y*z) = (y*b)*(z*c)*x := by ring
    have hh2: (y*b)*(z*c) ≡ 1 [ZMOD 13] := by
      rw [← mul_one 1]
      exact Int.ModEq.mul hy hz
    nth_rw 2 [← mul_one x]
    rw [hh1, mul_comm x 1]
    exact Int.ModEq.mul hh2 rfl
  have h6: c*a*(x*y*z) ≡ y [ZMOD 13] := by
    have hh1: c*a*(x*y*z) = (z*c)*(x*a)*y := by ring
    have hh2: (z*c)*(x*a) ≡ 1 [ZMOD 13] := by
      rw [← mul_one 1]
      exact Int.ModEq.mul hz hx
    nth_rw 2 [← mul_one y]
    rw [hh1, mul_comm y 1]
    exact Int.ModEq.mul hh2 rfl
  -- multiply xyz to h1,h2,h3, and simplify.
  -- multiply xyz to h1
  have heq1: 2*z+x+y ≡ 0 [ZMOD 13] := by
    have hh1: (2*a*b+b*c+c*a)*(x*y*z) ≡ 0 [ZMOD 13] := by
      have: 0 = 0*(x*y*z) := by simp
      rw [this]
      exact Int.ModEq.mul h1 rfl
    have hh2: (2*a*b+b*c+c*a)*(x*y*z) = 2*((a*b)*(x*y*z))+
      (b*c)*(x*y*z)+(c*a)*(x*y*z) := by ring
    have hh3: 2*((a*b)*(x*y*z))+(b*c)*(x*y*z)+(c*a)*(x*y*z)
      ≡ 2*((a*b)*(x*y*z))+(b*c)*(x*y*z) + y [ZMOD 13] := by
      apply Int.ModEq.add rfl h6
    have hh4: 2*((a*b)*(x*y*z))+(b*c)*(x*y*z) + y
      ≡ y+2*((a*b)*(x*y*z)) + x [ZMOD 13] := by
      rw [add_comm _ y, ← add_assoc]
      apply Int.ModEq.add rfl h5
    have hh5: y+2*((a*b)*(x*y*z))+x ≡ x+y+2*z [ZMOD 13] := by
      rw [add_comm _ x, ← add_assoc]
      have: 2*((a*b)*(x*y*z)) ≡ 2*z [ZMOD 13] := by
        exact Int.ModEq.mul_left 2 h4
      exact Int.ModEq.add rfl this
    have hh6: 2*z+x+y = x+y+2*z := by ring
    rw [hh6]
    rw [hh2] at hh1
    apply Int.ModEq.trans hh5.symm
    apply Int.ModEq.trans hh4.symm
    apply Int.ModEq.trans hh3.symm hh1
  -- multiply xyz to h2
  have heq2: z+2*x+y ≡ 6 [ZMOD 13] := by
    have hh1: (a*b+2*b*c+c*a)*(x*y*z) ≡ 6 [ZMOD 13] := by
      have tt1: (a*b+2*b*c+c*a)*(x*y*z)
        ≡ 6*a*b*c * (x*y*z) [ZMOD 13] := by
        exact Int.ModEq.mul h2 rfl
      have tt2: 6*a*b*c*(x*y*z) ≡ 6 [ZMOD 13] := by
        have htt1:6*a*b*c*(x*y*z) = 6 * (x*a)*(y*b)*(z*c) := by ring
        rw [htt1]
        have htt2: 6*(x*a)*(y*b)*(z*c) ≡ 6*(x*a)*(y*b) [ZMOD 13] := by
          nth_rw 2 [← mul_one (6*(x*a)*(y*b))]
          exact Int.ModEq.mul_left (6 * (x * a) * (y * b)) hz
        have htt3: 6*(x*a)*(y*b) ≡ 6*(x*a) [ZMOD 13] := by
          nth_rw 2 [← mul_one (6*(x*a))]
          exact Int.ModEq.mul_left (6 * (x * a)) hy
        have htt4: 6*(x*a) ≡ 6 [ZMOD 13] := by
          nth_rw 2 [← mul_one 6]
          exact Int.ModEq.mul_left 6 hx
        apply Int.ModEq.trans htt2 (Int.ModEq.trans htt3 htt4)
      exact Int.ModEq.trans tt1 tt2
    have hh2: (a*b+2*b*c+c*a)*(x*y*z) = (a*b)*(x*y*z)+
      2*((b*c)*(x*y*z))+(c*a)*(x*y*z) := by ring
    have hh3: (a*b)*(x*y*z)+2*((b*c)*(x*y*z))+(c*a)*(x*y*z)
      ≡ (a*b)*(x*y*z)+2*((b*c)*(x*y*z)) + y [ZMOD 13] := by
      apply Int.ModEq.add rfl h6
    have hh4: (a*b)*(x*y*z)+2*((b*c)*(x*y*z)) + y
      ≡ y+(a*b)*(x*y*z) + 2*x [ZMOD 13] := by
      rw [add_comm _ y, ← add_assoc]
      apply Int.ModEq.add rfl
      exact Int.ModEq.mul_left 2 h5
    have hh5: y+(a*b)*(x*y*z)+2*x ≡ 2*x+y+z [ZMOD 13] := by
      rw [add_comm _ (2*x), ← add_assoc]
      apply Int.ModEq.add rfl h4
    have hh6: z+2*x+y = 2*x+y+z := by ring
    rw [hh6]
    rw [hh2] at hh1
    apply Int.ModEq.trans hh5.symm
    apply Int.ModEq.trans hh4.symm (Int.ModEq.trans hh3.symm hh1)
  -- multiply xyz to h3
  have heq3: z+x+2*y ≡ 8 [ZMOD 13] := by
    have hh1: (a*b+b*c+2*c*a)*(x*y*z) ≡ 8 [ZMOD 13] := by
      have tt1: (a*b+b*c+2*c*a)*(x*y*z)
        ≡ 8*a*b*c*(x*y*z) [ZMOD 13] := by
        exact Int.ModEq.mul h3 rfl
      have tt2: 8*a*b*c*(x*y*z) = 8*(x*a)*(y*b)*(z*c) := by ring
      apply Int.ModEq.trans tt1
      rw [tt2]
      apply Int.ModEq.trans (Int.ModEq.mul_left (8*(x*a)*(y*b)) hz)
      simp
      apply Int.ModEq.trans (Int.ModEq.mul_left (8*(x*a)) hy)
      simp; nth_rw 2 [← mul_one 8]
      exact Int.ModEq.mul_left 8 hx
    have hh2: (a*b+b*c+2*c*a)*(x*y*z) = (a*b)*(x*y*z)
      + (b*c)*(x*y*z)+2*(c*a)*(x*y*z) := by ring
    have hh3: z+x+2*y ≡ z+x+2*(c*a)*(x*y*z) [ZMOD 13] := by
      apply Int.ModEq.add rfl
      rw [mul_assoc]
      apply Int.ModEq.mul_left 2 h6.symm
    have hh4: z+x+2*(c*a)*(x*y*z) ≡
      (a*b*(x*y*z))+(b*c*(x*y*z))+2*(c*a)*(x*y*z) [ZMOD 13] := by
      refine Int.ModEq.add ?_ rfl
      apply Int.ModEq.add h4.symm h5.symm
    apply Int.ModEq.trans hh3
    apply Int.ModEq.trans hh4
    rw [← hh2]; apply hh1
  -- now, let's add heq1, heq2, heq3 together
  have heq4: 4*(x+y+z) ≡ 14 [ZMOD 13] := by
    have hh1: 4*(x+y+z) = (2*z+x+y)+(z+2*x+y)+(z+x+2*y) := by ring
    have hh2: (14:ℤ) = 0+6+8 := by norm_num
    rw [hh1, hh2]
    apply Int.ModEq.add
    · apply Int.ModEq.add heq1 heq2
    · apply heq3
  -- and we can solve x+y+z ≡ 10 (mod 13)
  have heq5: x+y+z ≡ 10 [ZMOD 13] := by
    have hh1: 4*(x+y+z) ≡ 4*10 [ZMOD 13] := by
      apply Int.ModEq.trans heq4 rfl
    have hh2: (13:ℤ) = 13 / ↑(Int.gcd 13 4) := by
      have: (13:ℤ).gcd 4 = 1 := rfl
      rw [this]; simp
    rw [hh2]
    apply Int.ModEq.cancel_left_div_gcd (by norm_num) hh1
  -- and we know 2x+y+z, x+2y+z, x+y+2z, so x,y,z are also determined.
  have xeq: x ≡ 9 [ZMOD 13] := by
    have hh1: x = z+2*x+y - (x+y+z) := by ring
    have hh2: (9:ℤ) = (6+13)-10 := by norm_num
    rw [hh1, hh2]
    apply Int.ModEq.sub
    · apply Int.ModEq.trans heq2 rfl
    · apply heq5
  have yeq: y ≡ 11 [ZMOD 13] := by
    have hh1: y = (z+x+2*y)-(x+y+z) := by ring
    have hh2: (11:ℤ) = (8+13)-10 := by ring
    rw [hh1, hh2]
    refine Int.ModEq.sub ?_ heq5
    apply Int.ModEq.trans heq3 rfl
  have zeq: z ≡ 3 [ZMOD 13] := by
    have hh1: z = (2*z+x+y)-(x+y+z) := by ring
    have hh2: (3:ℤ) = (0+13)-10 := by ring
    rw [hh1, hh2]
    refine Int.ModEq.sub ?_ heq5
    apply Int.ModEq.trans heq1 rfl
  -- hereby a⁻¹, b⁻¹, c⁻¹ is determined and a,b,c < 13, 13 is prime, so a,b,c are also determined.
  -- 9a ≡ 1 (mod 13), a is from 0 to 13, so a = 3
  have aeq: a = 3 := by
    have hh1: 9*a ≡ 1 [ZMOD 13] := by
      have: 9*a ≡ x*a [ZMOD 13] := by
        apply Int.ModEq.mul xeq.symm rfl
      exact Int.ModEq.trans this hx
    have hh2: 9*a ≡ 9*3 [ZMOD 13] := by
      apply Int.ModEq.trans hh1 rfl
    have hh3: a ≡ 3 [ZMOD 13] := by
      have: (13:ℤ) = 13/↑(Int.gcd 13 9) := by norm_num
      rw [this]
      apply Int.ModEq.cancel_left_div_gcd (by norm_num) hh2
    have hh4: a.toNat ≡ 3 [MOD 13] := by
      rw [← an] at hh3
      exact Int.natCast_modEq_iff.mp hh3
    have hh5: a.toNat = 3 := by
      apply Nat.ModEq.eq_of_lt_of_lt hh4
      · have := ha.right
        rw [← an] at this
        exact Int.ofNat_lt.mp this
      · norm_num
    rw [← an, hh5]; simp
  -- 11b ≡ 1 (mod 13), b=6
  have beq: b = 6 := by
    have hh1: 11*b ≡ 1 [ZMOD 13] := by
      have: 11*b ≡ y*b [ZMOD 13] := by
        apply Int.ModEq.mul yeq.symm rfl
      exact Int.ModEq.trans this hy
    have hh2: 11*b ≡ 11*6 [ZMOD 13] := by
      apply Int.ModEq.trans hh1 rfl
    have hh3: b ≡ 6 [ZMOD 13] := by
      have: (13:ℤ) = 13/↑(Int.gcd 13 6) := by norm_num
      rw [this]
      apply Int.ModEq.cancel_left_div_gcd (by norm_num) hh2
    have hh4: b.toNat ≡ 6 [MOD 13] := by
      rw [← bn] at hh3
      exact Int.natCast_modEq_iff.mp hh3
    have hh5: b.toNat = 6 := by
      apply Nat.ModEq.eq_of_lt_of_lt hh4
      · have := hb.right
        rw [← bn] at this
        exact Int.ofNat_lt.mp this
      · norm_num
    rw [← bn, hh5]; simp
  -- 3c ≡ 1 (mod 13), c=9.
  have ceq: c = 9 := by
    have hh1: 3*c ≡ 1 [ZMOD 13] := by
      have: 3*c ≡ z*c [ZMOD 13] := by
        apply Int.ModEq.mul zeq.symm rfl
      exact Int.ModEq.trans this hz
    have hh2: 3*c ≡ 3*9 [ZMOD 13] := by
      apply Int.ModEq.trans hh1 rfl
    have hh3: c ≡ 9 [ZMOD 13] := by
      apply Int.ModEq.cancel_left_div_gcd (by norm_num) hh2
    have hh4: c.toNat ≡ 9 [MOD 13] := by
      rw [← cn] at hh3
      exact Int.natCast_modEq_iff.mp hh3
    have hh5: c.toNat = 9 := by
      apply Nat.ModEq.eq_of_lt_of_lt hh4
      · have := hc.right
        rw [← cn] at this
        exact Int.ofNat_lt.mp this
      · norm_num
    rw [← cn, hh5]; simp
  -- therefore, a+b+c = 3+6+9=18, mod 13 is 5.
  rw [aeq,beq,ceq]; simp; rfl