import Mathlib


/- 13. (NZL 1) ${ }^{\mathrm{IMO1}}$ Find all integer triples $(p, q, r)$ such that
$1 < p < q < r$ and $(p-1)(q-1)(r-1)$ is a divisor of $(p q r-1)$. -/
theorem number_theory_24412 (p q r : ℤ) (hpqr : 1 < p ∧ p < q ∧ q < r):
    ((p - 1) * (q - 1) * (r - 1) ∣ p * q * r - 1) ↔
    (p = 2 ∧ q = 4 ∧ r = 8) ∨ (p = 3 ∧ q = 5 ∧ r = 15) := by

  have hp: p-1 > 0 := by linarith only [hpqr]
  have hq: q-1 > 0 := by linarith only [hpqr]
  have hr: r-1 > 0 := by linarith only [hpqr]
  qify at hp hq hr

  -- let's define F (p,q,r) = (pqr-1) / ( (p-1)(q-1)(r-1) )
  set F : ℤ  → ℤ  → ℤ → ℚ := fun x y z =>
    (x*y*z-1) / ((x-1)*(y-1)*(z-1)) with F_def

  -- obviously, (p-1)(q-1)(r-1) F = pqr-1
  have hF1: (p-1)*(q-1)*(r-1) * (F p q r) = p*q*r - 1 := by
    simp only [F_def]
    field_simp [hp, hq, hr]

  -- simplify F
  have hF2 {x y z: ℤ} (hx: x-1 > (0:ℚ)) (hy: y-1 > (0:ℚ))
    (hz: z - 1 > (0:ℚ)):
    F x y z = 1 + 1/(x-1) + 1/(y-1) + 1/(z-1) +
    1/((x-1)*(y-1)) + 1/((y-1)*(z-1)) + 1/((z-1)*(x-1)) := by
    simp only [F_def]
    field_simp [hx, hy, hz]
    ring

  -- then F > 1
  have hF3: F p q r > 1 := by
    rw [hF2 hp hq hr]
    simp only [add_assoc, lt_add_iff_pos_right]
    positivity

  -- cannot be the case a divide b but a even b odd
  have dvd_odd {a b: ℤ} (h1: a ∣ b) (h2: Odd b): Odd a := by
    rw [← Int.not_even_iff_odd]
    rintro h3
    absurd h2
    rw [Int.not_odd_iff_even]
    exact Dvd.dvd.even h1 h3

  -- if a,b have same parity, b > a, then b ≥ a+2
  have ge2_of_same_pair {a b:ℤ} (h1: b > a)
    (h2: (Even a ∧ Even b) ∨ (Odd a ∧ Odd b)):
    b ≥ a+2 := by
    suffices b > a+1 by
      clear * - this
      omega
    apply lt_of_le_of_ne (by exact h1) ?_
    rintro rfl
    -- a and a+1 cannot have same pair, contradiction.
    rcases h2 with h2 | h2
    all_goals
      absurd h2; push_neg; intro ha
      simp only [Int.not_even_iff_odd, Int.not_odd_iff_even]
      simp only [ha, Odd.add_one, Even.add_one]


  -- if ab = p, p is prime adn 0 < a < b, then a = 1 and b = p
  have solve_eq {a b:ℤ} {pp:ℕ} (ha: 0 < a) (hb: a < b)
    (hp: Nat.Prime pp) (heq: a*b = pp): a = 1 ∧ b = pp := by
    have hb': 0 < b := by linarith only [ha, hb]
    have pdv: (pp:ℤ) ∣ a*b := by
      simp [heq]
    rcases (Int.Prime.dvd_mul' hp pdv) with hh | hh
    · -- cannot be p ∣ a, otherwise a = b = 1, therefore p =1.
      -- but p is prime, contradiction.
      replace hh := Int.le_of_dvd ha hh
      rw [← heq, mul_le_iff_le_one_right ha] at hh
      replace hh: b = 1 := by
        clear * - hh hb'
        omega
      replace ha: a = 1 := by
        clear * - ha hh hb
        rw [hh] at hb
        omega
      simp only [ha, hh, mul_one] at heq
      norm_cast at heq
      norm_num [← heq] at hp
    · -- if p divide b, then p = b, a = 1.
      replace hh := Int.le_of_dvd hb' hh
      rw [← heq, mul_le_iff_le_one_left hb'] at hh
      replace hh: a = 1 := by
        clear * - ha hh
        omega
      simp only [hh, one_mul] at heq
      exact ⟨hh, heq⟩

  constructor

  · intro hdvd
    -- we claim if (p-1)(q-1)(r-1) divide pqr-1, then p,q,r have same parity.
    have pqr_pairity: (Odd p ∧ Odd q ∧ Odd r) ∨ (Even p ∧ Even q ∧ Even r) := by
      rcases (Int.even_or_odd (p*q*r-1)) with hh | hh
      · replace hh: Odd (p*q*r) := by
          rw [← Int.sub_add_cancel (p*q*r) 1]
          apply Even.add_one hh
        left
        simp only [Int.odd_mul] at hh
        exact and_assoc.mp hh
      · replace hh := dvd_odd hdvd hh
        right
        simp only [Int.odd_mul] at hh
        rw [← Int.sub_add_cancel p 1,
        ← Int.sub_add_cancel q 1, ← Int.sub_add_cancel r 1]
        refine ⟨?_, ?_, ?_⟩
        all_goals
          apply Odd.add_one ?_
          simp [hh]

    -- the given divide relation is equivalent to F is integer.
    rcases hdvd with ⟨k,hk⟩
    qify at hk
    simp only [← hF1, mul_eq_mul_left_iff, mul_eq_zero,
    hp.ne', hq.ne', or_self, hr.ne', or_false] at hk
    -- F > 1 is an integer, then F ≥ 2.
    replace hF3: F p q r ≥ 2 := by
      rw [hk] at hF3 ⊢
      norm_cast at hF3 ⊢

    -- p,q,r have same pair, so q ≥ p+2, r ≥ q+2 ≥ p+4
    have hqp: q ≥ p+2 := by
      apply ge2_of_same_pair hpqr.right.left
      clear * - pqr_pairity
      tauto
    have hrq: r ≥ q+2 := by
      apply ge2_of_same_pair hpqr.right.right
      clear * - pqr_pairity
      tauto


    -- and F is decreasing

    -- if p1 ≤ p2, then F p1 ≥ F p2
    have Fdecp {p1 p2 q1 r1: ℤ} (h: p1 ≤ p2)
      (hp1: p1 - 1 > (0:ℚ)) (hp2: p2 - 1 > (0:ℚ))
      (hq1: q1 - 1 > (0:ℚ)) (hr1: r1 - 1 > (0:ℚ)):
      F p1 q1 r1 ≥ F p2 q1 r1 := by
      qify at h
      simp only [hF2 hp1 hq1 hr1, hF2 hp2 hq1 hr1]
      simp only [add_assoc, add_le_add_iff_left]
      have h1: (1:ℚ)/(p2-1) ≤ 1/(p1-1) := by
        apply one_div_le_one_div_of_le hp1 ?_
        linarith only [h]
      have h2: (1:ℚ)/((p2-1)*(q1-1)) ≤
        (1:ℚ)/((p1-1)*(q1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_right hq1).mpr ?_
          linarith only [h]
      have h3: (1:ℚ)/((r1-1)*(p2-1)) ≤ (1:ℚ)/((r1-1)*(p1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_left hr1).mpr ?_
          linarith only [h]
      linarith only [h1, h2, h3]

    -- if q1 ≤ q2, then F q1 ≥ F q2
    have Fdecq {q1 q2 p1 r1: ℤ} (h: q1 ≤ q2)
      (hq1: q1 - 1 > (0:ℚ)) (hq2: q2 - 1 > (0:ℚ))
      (hp1: p1 - 1 > (0:ℚ)) (hr1: r1 - 1 > (0:ℚ)):
      F p1 q1 r1 ≥ F p1 q2 r1 := by
      qify at h
      simp only [hF2 hp1 hq1 hr1, hF2 hp1 hq2 hr1]
      simp only [add_assoc, add_le_add_iff_left]
      have h1: (1:ℚ)/(q2-1) ≤ 1/(q1-1) := by
        apply one_div_le_one_div_of_le hq1 ?_
        linarith only [h]
      have h2: (1:ℚ)/((p1-1)*(q2-1)) ≤
        (1:ℚ)/((p1-1)*(q1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_left hp1).mpr ?_
          linarith only [h]
      have h3: (1:ℚ)/((q2-1)*(r1-1)) ≤ (1:ℚ)/((q1-1)*(r1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_right hr1).mpr ?_
          linarith only [h]
      linarith only [h1,h2,h3]


    -- if r1 ≤ r2, then F r1 ≥ F r2
    have Fdecr {q1 p1 r1 r2: ℤ} (h: r1 ≤ r2)
      (hr1: r1 - 1 > (0:ℚ)) (hr2: r2 - 1 > (0:ℚ))
      (hp1: p1 - 1 > (0:ℚ)) (hq1: q1 - 1 > (0:ℚ)):
      F p1 q1 r1 ≥ F p1 q1 r2 := by
      qify at h
      simp only [hF2 hp1 hq1 hr1, hF2 hp1 hq1 hr2]
      simp only [add_assoc, add_le_add_iff_left]
      have h1: (1:ℚ)/(r2-1) ≤ 1/(r1-1) := by
        apply one_div_le_one_div_of_le hr1 ?_
        linarith only [h]
      have h2: (1:ℚ)/((q1-1)*(r2-1)) ≤
        (1:ℚ)/((q1-1)*(r1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_left hq1).mpr ?_
          linarith only [h]
      have h3: (1:ℚ)/((r2-1)*(p1-1)) ≤ (1:ℚ)/((r1-1)*(p1-1)) := by
        apply one_div_le_one_div_of_le ?_ ?_
        · positivity
        · refine (mul_le_mul_iff_of_pos_right hp1).mpr ?_
          linarith only [h]
      linarith only [h1,h2,h3]


    -- impossible for p ≥ 4.
    have plt4: p < 4 := by
      by_contra! pge4
      -- when p ≥ 4, q ≥ 6 and r ≥ 8.
      have qge6: q ≥ 6 := by
        linarith only [hqp, pge4]
      -- similarly, we argue when q ≥ 6, r > q, q,r share same parity, r ≥ 8.
      have rge8: r ≥ 8 := by
        linarith only [hrq, qge6]

      -- therefore F pqr ≤ F 468
      have hF4: F p q r ≤ F 4 6 8 := by
        have h1: F p q r ≤ F 4 q r := by
          apply Fdecp pge4 (by norm_num) hp hq hr
        have h2: F 4 q r ≤ F 4 6 r := by
          apply Fdecq qge6 (by norm_num) hq (by norm_num) hr
        have h3: F 4 6 r ≤ F 4 6 8 := by
          apply Fdecr rge8 (by norm_num) hr (by norm_num) (by norm_num)
        linarith only [h1, h2, h3]

      -- however, F 468 < 2, contradiction.
      have: F 4 6 8 < 2 := by
        simp only [F_def]
        norm_num
      linarith only [hF3, hF4, this]

    -- p < 4 and p > 1, then p = 2,3.
    have peq: p = 2 ∨ p = 3 := by
      have := hpqr.left
      clear * - plt4 this
      omega

    rcases peq with peq | peq

    · -- when p = 2, F pqr ≤ F 2 4 6 < 4.
      have hF4: F p q r < 4 := by
        have h1: F p q r ≤ F 2 4 6 := by
          rw [peq] at hqp ⊢
          have h2: F 2 q r ≤ F 2 4 r := by
            apply Fdecq hqp (by norm_num) hq (by norm_num) hr
          have h3: F 2 4 r ≤ F 2 4 6 := by
            apply Fdecr ?_ (by norm_num) hr (by norm_num) (by norm_num)
            linarith only [hqp, hrq]
          linarith only [h2, h3]
        have h2: F 2 4 6 < 4 := by
          simp only [F_def]
          norm_num
        linarith only [h1, h2]

      -- then F p q r is 2 or 3.
      have hF5: F p q r = 2 ∨ F p q r = 3 := by
        rw [hk] at hF3 hF4 ⊢
        clear * - hF3 hF4
        norm_cast at hF3 hF4 ⊢
        omega

      rcases hF5 with hF5 | hF5
      · simp only [F_def, peq] at hF5
        norm_num at hF5
        -- the equation turns to 2pqr-1 = 2(q-1)(r-1)
        -- left side odd right side even, no solution.
        field_simp only [hq, hr] at hF5
        norm_cast at hF5
        have: Odd (2*((q-1)*(r-1))) := by
          rw [← hF5, mul_assoc]
          refine Even.sub_odd ?_ (by norm_num)
          exact even_two_mul (q * r)
        absurd this
        rw [Int.not_odd_iff_even]
        apply even_two_mul
      · simp only [F_def, peq] at hF5
        norm_num at hF5
        field_simp only [hq, hr] at hF5
        -- equation turns to 2qr-1 = 3(q-1)(r-1).
        -- or, (q-3)(r-3) = 5
        replace hF5: (q-3)*(r-3) = (5:ℚ) := by
          linarith only [hF5]
        norm_cast at hF5
        -- for (q-3)(r-3)=5 and q < r, only solution is q=4, r=8.
        -- since 5 is prime, so two factors must equal to 1 and 5.
        have: q-3 = 1 ∧ r-3 = ↑(5:ℕ) := by
          rw [peq] at hqp
          apply solve_eq (by linarith only [hqp]) ?_ (by norm_num) hF5
          linarith only [hqp, hrq]
        left
        norm_num at this
        refine ⟨peq, ?_, ?_⟩
        <;> linarith only [this]

    · -- now let p = 3.
      -- F 3 q r ≤ F 3 5 7 < 3
      have hF4: F p q r < 3 := by
        have h1: F p q r ≤ F 3 5 7 := by
          rw [peq] at hqp ⊢
          have h2: F 3 q r ≤ F 3 5 r := by
            apply Fdecq hqp (by norm_num) hq (by norm_num) hr
          have h3: F 3 5 r ≤ F 3 5 7 := by
            apply Fdecr ?_ (by norm_num) hr (by norm_num) (by norm_num)
            linarith only [hqp, hrq]
          linarith only [h2, h3]
        have h2: F 3 5 7 < 3 := by
          simp only [F_def]
          norm_num
        linarith only [h1, h2]

      -- then F p q r = 2
      have hF5: F p q r = 2 := by
        rw [hk] at hF3 hF4 ⊢
        clear * - hF3 hF4
        norm_cast at *
        omega

      simp only [peq, F_def] at hF5
      norm_num at hF5
      field_simp only [hq, hr] at hF5
      -- now ,equation is 3qr-1 = 4(q-1)(r-1).
      -- or, (q-4)(r-4) = 11
      replace hF5: (q-4)*(r-4) = (11:ℚ) := by
        linarith only [hF5]
      norm_cast at hF5
      -- we solve q = 5 and r = 15
      have: q-4 = 1 ∧ r-4 = ↑(11:ℕ) := by
        rw [peq] at hqp
        apply solve_eq ?_ ?_ (by norm_num) hF5
        <;> linarith only [hqp, hrq]
      norm_num at this
      right
      refine ⟨peq, ?_, ?_⟩
      <;> linarith only [this]


  · -- verification
    rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    <;> norm_num