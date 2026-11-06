import Mathlib


/- Find all pairs $(a, b)$ of positive integers such that $a!+b$ and $b!+a$ are both powers of 5 . -/
theorem number_theory_605583 (a b : ℕ) (posa: 0 < a) (posb: 0 < b) :
    (∃ m n, Nat.factorial a + b = 5 ^ m ∧ Nat.factorial b + a = 5 ^ n) ↔
    (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨ (a = 5 ∧ b = 5) := by
  -- condition is symmetric, we may assume b ≤ a.
  wlog blea: b ≤ a
  · push_neg at blea
    replace := this b a posb posa (le_of_lt blea)
    constructor
    · rintro ⟨m,n,hb,ha⟩
      replace := this.mp ⟨n,m,ha,hb⟩
      tauto
    · intro h
      replace := this.mpr (by tauto)
      tauto
  constructor
  · rintro ⟨m, n, hm, hn⟩
    -- given a!+b, b!+a are 5-power, find a,b.
    -- first, we prove only solution to x!+1 = 5^k is x=4
    have solve_eq {x k: ℕ} (posk: 0 < k) (h: x.factorial + 1 = 5^k):
      x = 4 := by
      have hdvd: 5 ∣ x.factorial + 1 := by
        rw [h]
        exact dvd_pow_self 5 posk.ne'
      -- cannot be the case x ≥ 5.
      have h1: x < 5 := by
        by_contra! xge
        -- if x ≥ 5, 5 ∣ x!. but we can also prove 5 ∣ x!+1
        -- therefore 5 ∣ 1, contradiction.
        have hdvd': 5 ∣ x.factorial := by
          exact Nat.dvd_factorial (by norm_num) xge
        have: 5 ∣ 1 := by
          exact (Nat.dvd_add_iff_right hdvd').mpr hdvd
        norm_num at this
      -- also, by verifying x = 0,1,2,3, we find cannot x must ≥ 4.
      -- 0!+1 = 1!+1 = 2, not 5-power. 2!+1 = 3 not 5-power.
      -- 3!+1 = 7 not 5-power.
      have h2: x ≥ 4 := by
        by_contra! hx
        replace hx: x ≤ 3 := Nat.le_of_lt_succ hx
        interval_cases x
        all_goals norm_num [← Nat.mul_factorial_pred] at hdvd
      -- so x=4 is the only solution
      exact Nat.eq_of_le_of_lt_succ h2 h1
    -- and obviously, m,n > 0. otherwise a!+b or b!+a = 1, which is impossible since a,b > 0.
    have pos_mn {m' c d: ℕ} (posd: 0 < d)
      (h: c.factorial + d = 5^m'): 0 < m' := by
      by_contra! mz
      replace mz: m' = 0 := Nat.eq_zero_of_le_zero mz
      simp only [mz, pow_zero] at h
      have h1: 1 ≤ d := by exact posd
      have h2: 1 ≤ c.factorial := by
        exact Nat.add_one_le_iff.mpr c.factorial_pos
      have not_h: 2 ≤ 1 := by
        rw [← h]
        linarith only [h1, h2]
      simp at not_h
    have posm := pos_mn posb hm
    have posn := pos_mn posa hn
    -- next, we suppose a = b. and we will show a=b=5 is a solution.
    have case_aeqb (aeqb: a = b): a = 5 ∧ b = 5 := by
      -- a! + a = 5^m, or a((a-1)!+1) = 5^m.
      replace hm: a * ((a-1).factorial + 1) = 5^m := by
        rw [← hm, ← aeqb, ← Nat.mul_factorial_pred posa]
        simp only [Nat.mul_add, mul_one]
      -- (a-1)! + 1 divide 5^m, then it is also 5-power.
      obtain ⟨k, hk⟩: ∃k, (a-1).factorial + 1 = 5^k := by
        have: (a-1).factorial + 1 ∣ 5^m := by
          rw [← hm]
          apply Nat.dvd_mul_left
        rw [Nat.dvd_prime_pow (by norm_num)] at this
        tauto
      -- (a-1)!+1 = 5^k, so a-1 = 4
      have ha: a-1 = 4 := by
        apply solve_eq ?_ hk
        apply pos_mn (by norm_num) hk
      -- then a = 5. and we suppose b = a, so b is also 5.
      replace ha: a = 5 := by omega
      simp [ha, ← aeqb]
    -- now assume b = 1. in this case, we find a=4, b=1 is a solution.
    -- recall that we suppose b ≤ a at very beginnng.
    -- so here swap a,b, in fact we have two solutions: (a,b) = (4,1) or (1,4).
    have case_beq1 (beq1: b = 1): a = 4 := by
      -- if b = 1, a! + 1 = 5^m.
      rw [beq1] at hm
      -- solve a!+1 = 5^m, a=4.
      apply solve_eq posm hm
    -- next, we show 1 < b < a is impossible.
    have case_b_not1 (bgt: 1 < b): b = a := by
      by_contra! blta
      replace blta: b < a := lt_of_le_of_ne blea blta
      -- we claim b is 5-power. it's because a!+b is 5-power and b ∣ a!.
      obtain ⟨z, zlem, hz⟩: ∃ z, z ≤ m ∧  b = 5^z := by
        -- b < a, then b ∣ a!
        have h1: b ∣ a.factorial := Nat.dvd_factorial posb blea
        -- therefore b ∣ 5^m.
        have h2: b ∣ 5^m := by
          rw [← hm]
          exact Nat.dvd_add_self_right.mpr h1
        -- so b is 5-power
        apply (Nat.dvd_prime_pow (by norm_num)).mp h2
      -- 1 < b = 5^z, so z ≥ 1.
      have znz: z ≠ 0 := by
        by_contra!
        simp [hz, this] at bgt
      -- b!+a = 5^n, then 5 ∣ a
      have h1: 5 ∣ a := by
        have hh1: 5 ∣ b.factorial + a := by
          rw [hn]
          refine dvd_pow_self 5 posn.ne'
        have hh2: 5 ∣ b.factorial := by
          have: 5 ∣ b := by
            rw [hz]
            exact dvd_pow_self 5 znz
          rw [← Nat.mul_factorial_pred posb]
          apply Dvd.dvd.mul_right this
        exact (Nat.dvd_add_iff_right hh2).mpr hh1
      -- a! = b! × (b+1)(b+2)...(b+a-b)
      -- so a! divided by b and contain factor a. or, divided by ab.
      have h2: b*a ∣ a.factorial := by
        rw [← Nat.mul_factorial_pred posa, mul_comm b a]
        have: b ∣ (a-1).factorial := by
          refine Nat.dvd_factorial posb ?_
          exact (Nat.le_sub_one_iff_lt posa).mpr blta
        exact Nat.mul_dvd_mul_left a this
      -- suppose a! = b (ac)
      rcases h2 with ⟨c, hc⟩
      -- then a! + b = b(ac+1)  = 5^m
      -- divide b from both sides, since b = 5^z, we have ac+1 = 5^(m-z)
      have h3: a*c+1 = 5^(m-z) := by
        rw [← Nat.pow_div zlem (by norm_num),
        ← hz, ← hm, hc, mul_assoc, ← mul_add_one]
        exact (Nat.mul_div_right (a * c + 1) posb).symm
      -- m > z because 5^m = a!+b > b = 5^z
      have hmz: 0 < m-z := by
        apply Nat.zero_lt_sub_of_lt
        have: 5^z < 5^m := by
          rw [← hz, ← hm]
          linarith only [a.factorial_pos]
        apply (pow_lt_pow_iff_right₀ (by norm_num)).mp this
      -- then 5 ∣ ac+1 and 5 ∣ a, therefore 5 ∣ 1. contradiction
      have: 5 ∣ 1 := by
        have h4: 5 ∣ a*c + 1 := by
          rw [h3]
          refine dvd_pow_self 5 hmz.ne'
        have h5: 5 ∣ a*c := by
          exact Dvd.dvd.mul_right h1 c
        exact (Nat.dvd_add_iff_right h5).mpr h4
      norm_num at this
    -- therefore we consider all possible cases, and can close the proof.
    by_cases hab: a = b
    · simp [case_aeqb hab]
    · by_cases hb: b = 1
      · simp [case_beq1 hb, hb]
      · have not_hab: b = a := by
          apply case_b_not1
          omega
        symm at not_hab
        contradiction
  · -- verification
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · use 1,2
      norm_num [← Nat.mul_factorial_pred]
    · use 2,1
      norm_num [← Nat.mul_factorial_pred]
    · use 3,3
      norm_num [← Nat.mul_factorial_pred]