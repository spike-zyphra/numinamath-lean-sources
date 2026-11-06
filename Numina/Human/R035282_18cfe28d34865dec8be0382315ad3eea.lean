import Mathlib

/- Es sei $p$ eine Primzahl. Weiter seien $a, b, c$ ganze Zahlen, welche die Gleichungen $a^{2}+p b=b^{2}+p c=c^{2}+p a$ erfüllen.
Man beweise, dass dann $a=b=c$ gilt. -/
theorem number_theory_604539{p:ℕ} (a b c : ℤ) (hp : Nat.Prime p)
    (h1 : a^2 + p * b = b^2 + p * c) (h2 : b^2 + p * c = c^2 + p * a) :
    a = b ∧ b = c := by
  -- we may assume a ≠ b, a ≠ c, b ≠ c. otherwise a=b=c easily follows from any two are equal.
  have{x y z: ℤ}(h: x=y)(eq1: x^2 + p*y = y^2+p*z)(eq2: y^2+p*z = z^2+p*x):
    x=y ∧ y=z := by
    rw [h, add_right_inj] at eq1
    have pnz: (p:ℤ) ≠ 0 := by
      simp [hp.ne_zero]
    simp only [h, (Int.mul_eq_mul_left_iff pnz).mp eq1, and_self]
  by_cases habc: a=b ∨ a=c ∨ b=c
  · rcases habc with hab | hac | hbc
    · apply this hab h1 h2
    · replace: c = a ∧ a = b := by
        apply this hac.symm ?_ h1
        apply h2.symm.trans h1.symm
      exact ⟨this.right, this.right.symm.trans this.left.symm⟩
    · replace: b = c ∧ c = a := by
        apply this hbc h2 ?_
        rw [h1, h2]
      rw [hbc, ← this.right, and_self]
  -- now a,b,c are pairwise distinct.
  push_neg at habc
  obtain ⟨hab, hac, hbc⟩ := habc
  -- if a^2 + pb = b^2 + pc, then move p-term to one side, we have
  -- p(c-b) = a^2-b^2, or p = (a+b)(a-b)/(c-b)
  have h3{x y z: ℤ}(h: x^2 + p*y = y^2 + p*z)(hzy: z ≠ y):
    p = (x+y) * (x-y) / (z-y) ∧ z-y ∣ (x+y)*(x-y) := by
    have hh1: p * (z-y) = (x+y) * (x-y) := by nlinarith [h]
    have hh2: z-y ≠ 0 := sub_ne_zero_of_ne hzy
    refine ⟨(Int.ediv_eq_of_eq_mul_left hh2 hh1.symm).symm, ?_⟩
    use p; rw [← hh1]; ring
  -- so p = (a+b)(a-b)/(c-b) = (b+c)(b-c)/(a-c) = (c+a)(c-a)/(b-a)
  -- mul them together, p^3 = -(a+b)(b+c)(c+a)
  have hp3: p^3 = - (a+b) * (b+c) * (c+a) := by
    rw [pow_three]
    have hh1: p = (a+b)*(a-b)/(c-b) ∧ c-b ∣ (a+b)*(a-b) := by
      apply h3 h1 hbc.symm
    have hh2: p = (b+c)*(b-c)/(a-c) ∧ a-c ∣ (b+c)*(b-c) := by
      apply h3 h2 hac
    have hh3: p = (c+a)*(c-a)/(b-a) ∧ b-a ∣ (c+a)*(c-a) := by
      apply h3 ?_ hab.symm
      rw [h1, h2]
    nth_rw 1 [hh1.left, hh2.left, hh3.left]
    have cbnz: ↑(c-b) ≠ (0:ℚ) := by
      norm_cast
      apply sub_ne_zero_of_ne hbc.symm
    have acnz: ↑(a-c) ≠ (0:ℚ) := by
      norm_cast
      apply sub_ne_zero_of_ne hac
    have banz: ↑(b-a) ≠ (0:ℚ) := by
      norm_cast
      apply sub_ne_zero_of_ne hab.symm
    qify
    rw [Int.cast_div hh1.right cbnz, Int.cast_div hh2.right acnz,
    Int.cast_div hh3.right banz]
    push_cast at cbnz acnz banz
    field_simp [banz, acnz, cbnz]
    ring
  -- a+b, b+c, c+a contain at least one even number, i.e., 2 ∣ p^3.
  -- since p,2 are prime, p can only be 2.
  replace hp: p = 2 := by
    suffices (2:ℤ) ∣ p^3 by
      norm_cast at this
      replace: 2 ∣ p := Nat.Prime.dvd_of_dvd_pow (by norm_num) this
      apply (Nat.Prime.dvd_iff_eq hp (by norm_num)).mp this
    suffices Even ((a+b)*((b+c)*(c+a))) by
      apply even_iff_two_dvd.mp ?_
      apply even_neg.mp ?_
      rwa [hp3, mul_assoc, Int.neg_mul, neg_neg]
    -- (a+b)(b+c)(c+a) is even, because no matter a,b,c even or odd
    -- one of these sums must be even.
    simp only [Int.even_mul]
    by_cases ha: Even a
    · by_cases hb: Even b
      · left; exact Even.add ha hb
      · by_cases hc: Even c
        · right; right
          apply Even.add hc ha
        · right; left
          rw [Int.not_even_iff_odd] at hb hc
          apply Odd.add_odd hb hc
    · rw [Int.not_even_iff_odd] at ha
      by_cases hb: Odd b
      · left; exact Odd.add_odd ha hb
      · by_cases hc: Odd c
        · right; right
          apply Odd.add_odd hc ha
        · right; left
          rw [Int.not_odd_iff_even] at hb hc
          apply Even.add hb hc
  -- p=2, therefore (a+b)(b+c)(c+a) = -8
  have heq: (a+b)*(b+c)*(c+a) = -8 := by
    simp only [hp, Nat.cast_ofNat, Int.reducePow] at hp3
    linarith [hp3]
  -- since we suppose a,b,c are pairwise distinct
  -- here we have a+b, b+c, c+a also pairwise distinct
  have hadd: a+b ≠ b+c ∧ b+c ≠ c+a ∧  c+a ≠ a+b := by
    by_contra!
    have hh1: a+b ≠ b+c := by
      rw [add_comm b c]
      rintro h
      simp only [add_left_inj] at h
      contradiction
    have hh2: b+c ≠ c+a := by
      rw [add_comm c a]
      rintro h
      simp only [add_left_inj] at h
      simp only [h, ne_eq, not_true_eq_false] at hab
    have hh3: c = b := by
      replace := this hh1 hh2
      rwa [add_comm c a, add_right_inj] at this
    simp [hh3] at hbc
  -- and a+b + b+c + c+a = 2(a+b+c) is even
  have add_even: Even ((a+b) + (b+c) + (c+a)) := by
    have: a+b+(b+c)+(c+a) = 2*(a+b+c) := by ring
    rw [this]
    exact even_two_mul (a + b + c)
  -- but we can prove this leads to a contradiction.
  -- first, clearly, if positive x ∣ 8, then x = 1,2,4,8.
  have dvd8(x:ℤ)(hx: 0 ≤ x)(hdvd: x ∣ 8): x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 := by
    have xle: x ≤ 8 := Int.le_of_dvd (by norm_num) hdvd
    clear * - hx hdvd xle
    revert hdvd
    revert xle hx x
    decide
  -- next, we prove if non-negative x+y+z is even and xyz = 8,
  -- then only two case: 2,2,2;  1,1,8.
  -- 1,2,4 is forbidden because 1+2+4 is odd.
  have{x y z: ℤ}(h4: Even (x+y+z))(hx: 0 ≤ x)(hy: 0 ≤ y)(hz: 0 ≤ z)
    (heq: x*y*z = 8): (x = 2 ∧ y = 2 ∧ z = 2) ∨ (x=8 ∨ y=8 ∨ z=8) := by
    -- if xy = 4, then x,y = 1,2,4.
    have dvd4{y': ℤ}(x':ℤ)(hx': 0 ≤ x')(hdvd: x'*y' = 4):
      x' = 1 ∨ x' = 2 ∨ x' = 4 := by
      replace hdvd: x' ∣ 4 := by
        rw [← hdvd]
        apply Int.dvd_mul_right
      have xle: x' ≤ 4 := Int.le_of_dvd (by norm_num) hdvd
      clear * - hx' xle hdvd
      revert hdvd
      revert xle hx' x'
      decide
    -- if xy = 2, then x = 1 or 2
    have dvd2(h: x*y = 2): x = 1 ∨ x = 2 := by
      replace h: x ∣ 2 := by
        rw [← h]
        apply Int.dvd_mul_right
      have xle := Int.le_of_dvd (by norm_num) h
      interval_cases x
      · simp at heq
      all_goals simp
    have odd7: ¬ Even 7 := by exact Nat.not_even_iff.mpr rfl
    obtain z1 | z2 | z4 | z8: z=1 ∨ z=2 ∨ z=4 ∨ z=8 := by
      apply dvd8 z hz
      rw [← heq]
      exact Int.dvd_mul_left (x * y) z
    · -- z=1 case.
      rw [z1, mul_one] at heq
      obtain y1 | y2 | y4 | y8: y=1 ∨ y=2 ∨ y=4 ∨ y=8 := by
        apply dvd8 y hy
        rw [← heq]
        exact Int.dvd_mul_left x y
      · -- z=1,y=1. then x=8
        rw [y1, mul_one] at heq
        simp [heq]
      · -- z=1,y=2. then x=4.
        have x4: x = 4 := by
          rw [y2] at heq
          linarith [heq]
        -- 1+2+4 is odd, contradiction
        simp only [x4, y2, Int.reduceAdd, z1] at h4
        contradiction
      · -- z=1, y=4. then x=2
        have x2: x = 2 := by
          rw [y4] at heq
          linarith [heq]
        simp only [x2, y4, Int.reduceAdd, z1] at h4
        contradiction
      · -- z=1, y=8.
        simp [y8]
    · -- z=2 case.
      have: x*y = 4 := by
        rw [z2] at heq
        linarith [heq]
      rcases (dvd4 x hx this) with x1 | x2 | x4
      · -- x=1, z=2.
        rw [x1, one_mul] at this
        simp only [z2, this, x1, Int.reduceAdd] at h4
        contradiction
      · -- x=2,z=2.
        left
        refine ⟨x2, ?_, z2⟩
        rw [x2] at this
        linarith [this]
      · -- x=4, z=2.
        have y1: y = 1 := by
          rw [x4] at this
          linarith [this]
        simp only [x4, y1, Int.reduceAdd, z2] at h4
        contradiction
    · -- z=4 case.
      have: x*y = 2 := by
        rw [z4] at heq
        linarith [heq]
      rcases (dvd2 this) with x1 | x2
      · -- z=4, x=1.
        rw [x1, one_mul] at this
        simp only [x1, this, Int.reduceAdd, z4] at h4
        contradiction
      · -- z=4, x=2.
        replace: y = 1 := by
          rw [x2] at this
          linarith [this]
        exfalso; apply odd7
        simp only [x2, this, Int.reduceAdd, z4] at h4
        exact (Int.even_coe_nat 7).mp h4
    · -- z=8
      simp [z8]
  -- a+b, b+c, c+a are pairwise distinct.
  -- easy to argue they cannot all be 2, so must be the case one of them is 8.
  replace{x y z:ℤ}(h4: Even (x+y+z))(h5: x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (heq: x*y*z = -8): x=8 ∨ y=8 ∨ z=8 := by
    clear * - h4 h5 this heq
    have h4': Even (|x|+|y|+|z|) := by
      refine Int.even_add.mpr ?_
      rw [Int.even_add] at h4
      rw [even_abs, ← h4]
      simp only [Int.even_add, even_abs]
    obtain (hh | hh): (|x|=2 ∧ |y|=2 ∧ |z|=2) ∨ (|x|=8 ∨ |y|=8 ∨ |z|=8) := by
      apply this h4' (abs_nonneg x) (abs_nonneg y) (abs_nonneg z) ?_
      simp only [← abs_mul, heq, Int.reduceNeg, abs_neg, Nat.abs_ofNat]
    · -- x,y,z cannot all has absolute value 2.
      -- otherwise 8 = -2 x 2 x 2, must have two of them equal.
      -- but we suppose x,y,z distinct.
      have nng_2: 0 ≤ (2:ℤ) := by norm_num
      simp only [abs_eq nng_2] at hh
      replace hh: x = y ∨ x = z := by
        obtain (y2 | yn2) := hh.right.left
        · obtain (z2 | zn2) := hh.right.right
          · simp [y2, z2] at h5
          · rw [y2, zn2]; exact hh.left
        · obtain (z2 | zn2) := hh.right.right
          · rw [yn2, z2]; symm; exact hh.left
          · simp [yn2, zn2] at h5
      tauto
    · -- if one of x,y,z is 8, then it must be of the form -1 x 1 x 8
      have nng_8: 0 ≤ (8:ℤ) := by norm_num
      -- cannot be -8, because otherwise other two number mul is 1.
      -- then they both are 1 or -1, contradiction.
      have{x' y' z': ℤ}(hne: y' ≠ z')(heq: x' * y' * z' = -8):
        x' ≠ -8 := by
        rintro xeq
        have: y' * z' = 1 := by
          rw [mul_assoc, xeq] at heq
          linarith [heq]
        rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
        rcases this with h1 | h1
        all_goals simp [h1] at hne
      simp only [abs_eq nng_8] at hh
      rcases hh with hh | hh | hh
      · have: x ≠ -8 := by
          apply this h5.right.right heq
        simp only [this, or_false] at hh
        simp [hh]
      · have: y ≠ -8 := by
          apply this h5.right.left
          rw [← heq]; ring
        simp only [this, or_false] at hh
        simp [hh]
      · have: z ≠ -8 := by
          apply this h5.left
          rw [← heq]; ring
        simp only [this, or_false] at hh
        simp [hh]
  simp only [hp, Nat.cast_ofNat] at h1 h2
  -- but x,y,z cannot be 8.
  -- otherwise does not satisfy equation a^2+2b = b^2+2c, b^2+2c = c^2 + 2a.
  have solve_eq{x y z: ℤ}(eq1: x+y = 8)(eq2: y+z = 1)(eq3: z+x = -1):
    x = 3 ∧ y = 5 ∧ z = -4 := by
    have hh1: x-z = 7 := by
      have: x-z = (x+y) - (y+z) := by ring
      simp [this, eq1, eq2]
    have hh2: x = 3 := by
      have: 2*x = z+x + (x-z) := by ring
      rw [eq3, hh1] at this
      linarith [this]
    rw [hh2] at eq1 eq3
    exact ⟨hh2, (by linarith [eq1]), (by linarith [eq3])⟩
  -- if we solve a=3, b=5, z=-4, substitute in a^2+2b = b^2+2c
  -- left side = 19, right side = 17, contradiction.
  -- since x,y,z are cyclic, we can always get such contradiction.
  replace hadd: a+b ≠ b+c ∧ a+b ≠ c+a ∧ b+c ≠ c+a := by tauto
  rcases (this add_even hadd heq) with hh1 | hh1 | hh1
  · -- a+b = 8, (b+c)(c+a) = -1.
    have hh2: (b+c)*(c+a) = -1 := by
      rw [hh1] at heq
      linarith [heq]
    rcases (Int.eq_one_or_neg_one_of_mul_eq_neg_one' hh2) with hh2 | hh2
    · -- b+c = 1, c+a = -1, a+b = 8.
      obtain ⟨aeq, beq, ceq⟩ := solve_eq hh1 hh2.left hh2.right
      simp [aeq, beq, ceq] at h1
    · rw [add_comm a b] at hh1
      rw [add_comm c a, add_comm b c] at hh2
      obtain ⟨beq, aeq, ceq⟩ := solve_eq hh1 hh2.right hh2.left
      simp [beq, aeq, ceq] at h1
  · -- b+c = 8, (c+a)(a+b) = -1.
    have hh2: (c+a)*(a+b) = -1 := by
      rw [hh1] at heq
      linarith [heq]
    rcases (Int.eq_one_or_neg_one_of_mul_eq_neg_one' hh2) with hh2 | hh2
    · -- b+c = 8, c+a = 1, a+b = -1
      obtain ⟨beq, ceq, aeq⟩  := solve_eq hh1 hh2.left hh2.right
      simp [beq, ceq, aeq] at h1
    · -- a+b = 1, c+a = -1.
      rw [add_comm b c] at hh1
      rw [add_comm a b, add_comm c a] at hh2
      have := solve_eq hh1 hh2.right hh2.left
      simp [this] at h1
  · -- c+a = 8, (a+b)(b+c) = -1.
    have hh2: (a+b)*(b+c) = -1 := by
      rw [hh1] at heq
      linarith [heq]
    rcases (Int.eq_one_or_neg_one_of_mul_eq_neg_one' hh2) with hh2 | hh2
    · have := solve_eq hh1 hh2.left hh2.right
      simp [this] at h1
    · rw [add_comm c a] at hh1
      rw [add_comm a b, add_comm b c] at hh2
      have := solve_eq hh1 hh2.right hh2.left
      simp [this] at h1