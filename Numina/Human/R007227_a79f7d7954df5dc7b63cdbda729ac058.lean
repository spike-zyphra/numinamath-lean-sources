import Mathlib

/- Find all pairs $(x, y)$ of integers such that $y^{3}-1=x^{4}+x^{2}$. -/
theorem number_theory_605046 (x y : ℤ) :
  y^3 - 1 = x^4 + x^2 ↔ (x, y) = (0, 1) := by
  -- we may suppose x ≥ 0, because x^4 and x^2 remain unchanged no matter x ≥ 0 or < 0.
  wlog x_nng: x ≥ 0
  · push_neg at x_nng
    have h1 := this (-x) y (by linarith [x_nng])
    have h2: (-x)^4 = x^4 := by
      rw [neg_pow]; simp
    simp [h2] at h1
    simp [h1]
  -- if a^3 ≥ 0, then a ≥ 0
  have lemma_nng_of_cube_nng{a:ℤ}(h: 0 ≤ a^3):
    0 ≤ a := by
    have: 3 = 2+1 := by norm_num
    rw [this, pow_succ] at h
    by_cases ha: a = 0
    · simp [ha]
    have hasq: 0 < a^2 := pow_two_pos_of_ne_zero ha
    exact nonneg_of_mul_nonneg_right h hasq
  -- next, we prove it cannot be the case x ≥ 1
  -- if x^2+x+1, x^2-x+1 are both cube terms.
  have case_xge1{a b: ℤ}
    (ha: x^2+x+1 = a^3)(hb: x^2-x+1 = b^3):
    x < 1 := by
    by_contra! hx
    have a_nng: 0 ≤ a := by
      apply lemma_nng_of_cube_nng ?_
      rw [← ha]; nlinarith [hx]
    have b_nng: 0 ≤ b := by
      apply lemma_nng_of_cube_nng ?_
      rw [← hb]; nlinarith [hx]
    -- obviously, a^3 > b^3, therefore a > b
    have agtb: a > b := by
      have: a^3 > b^3 := by
        rw [← ha, ← hb]
        linarith [hx]
      apply (pow_lt_pow_iff_left₀ b_nng a_nng (by norm_num)).mp this
    -- or, a ≥ b+1
    replace agtb: a ≥ b+1 := by exact agtb
    -- in fact, we can verify a ≥ 3.
    -- i.e., a cannot be 0,1,2
    have age: a ≥ 3 := by
      by_contra! ale
      replace ale: a ≤ 2 := by omega
      interval_cases a
      · simp at ha
        -- a=0.
        -- impossible for x^2+x+1 = 0 given x is integer
        omega
      · simp at ha
        -- a=1
        -- x^2+x = 0, impossible when x ≥ 1
        nlinarith [ha, hx]
      · simp at ha
        -- a=2
        -- x^2+x+1 = 8, or x(x+1) = 7
        replace hx: x*(x+1) = 7 := by linarith [ha]
        -- but 7 is prime, contradiction.
        rw [← Int.toNat_of_nonneg x_nng] at hx
        have hx1: x.toNat ∣ 7 := by
          zify; rw [← hx]
          exact Int.dvd_mul_right _ _
        have hx2: x.toNat = 1 ∨ x.toNat = 7 := by
          apply (Nat.dvd_prime (by norm_num)).mp hx1
        rcases hx2 with xeq | xeq
        all_goals simp [xeq] at hx
    -- now we show  x^2+x+1 - 2x =  x^2-x+1 ≤ x^2+x+1 - 2a^2
    have hineq: (x^2+x+1) - 2*x < (x^2+x+1) - 2*a^2 := calc
      (x^2+x+1) - 2*x = x^2-x+1 := by ring
      _ = b^3 := by rw [hb]
      _ ≤ (a-1)^3 := by
        have: b ≤ a-1 := by linarith [agtb]
        apply (pow_le_pow_iff_left₀ b_nng ?_ (by norm_num)).mpr this
        apply le_trans b_nng this
      _ = a^3-3*a^2+3*a-1 := by ring
      _ < a^3-3*a^2+3*a := by linarith
      _ = a^3-2*a^2 + a*(3-a) := by ring
      _ ≤ a^3-2*a^2 := by
        have: a*(3-a) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos a_nng
          linarith [age]
        linarith [this]
      _ = _ := by rw [← ha]
    -- therefore x > a^2
    have xgt: x > a^2 := by linarith [hineq]
    -- but it's impossible for x > a^2
    have not_xgt: x ≤ a^2 := by
      have h1: (a^2)^2 ≥ a^3 := by
        have: (a^2)^2 = a * a^3 := by ring
        rw [this]
        apply le_mul_of_one_le_left ?_ (by linarith [age])
        rw [← ha]; nlinarith [hx]
      have h2: x^2 ≤ (a^2)^2 := calc
        x^2 ≤ x^2+x+1 := by linarith [hx]
        _ = a^3 := by rw [ha]
        _ ≤ _ := h1
      apply (pow_le_pow_iff_left₀ ?_ (sq_nonneg a) (by norm_num)).mp h2
      linarith [hx]
    linarith [xgt, not_xgt]
  -- back to the problem
  constructor
  · intro heq
    -- add 1 to both sides of y^3-1 = x^4+x^2
    -- we get y^3 = (x^2+x+1)(x^2-x+1)
    replace heq:y^3 = (x^2+x+1)*(x^2-x+1) := by
      have: y^3 = y^3-1+1 := by ring
      rw [this, heq]; ring
    -- x^2+x+1 and x^2-x+1 are coprime
    have h2: IsCoprime (x^2+x+1) (x^2-x+1) := by
      have nng_1: 0 ≤ x^2+x+1 := by nlinarith [x_nng]
      have nng_2: 0 ≤ x^2-x+1 := by nlinarith [x_nng]
      have le_12: (x^2-x+1).toNat ≤ (x^2+x+1).toNat := by
        simp; left; linarith [x_nng]
      have: Nat.Coprime (x^2+x+1).toNat (x^2-x+1).toNat := by
        apply Nat.coprime_of_dvd' ?_
        intro p pp h1 h2
        -- if p divide these two, then p divide their sub
        have h3: p ∣ 2*x.toNat := by
          have: 2*x.toNat = (x^2+x+1).toNat - (x^2-x+1).toNat := by
            zify; rw [Int.toNat_of_nonneg x_nng]
            rw [Nat.cast_sub le_12, Int.toNat_of_nonneg nng_1,
            Int.toNat_of_nonneg nng_2]; ring
          rw [this]
          exact Nat.dvd_sub le_12 h1 h2
        have hodd: Odd (x^2+x+1) := by
          have: Even (x^2+x) := by
            refine Int.even_add'.mpr ?_
            apply Int.odd_pow' (by norm_num)
          exact Even.add_one this
        rw [← Int.toNat_of_nonneg nng_1] at hodd
        norm_cast at hodd
        -- then p cannot divide 2, p divide x.
        have hh2: p ∣ x.toNat := by
          rw [Nat.Prime.dvd_mul pp] at h3
          rcases h3 with h31 | h32
          · rw [Nat.Prime.dvd_iff_eq (by norm_num)
            (Nat.Prime.ne_one pp)] at h31
            simp [← h31] at h1
            rcases h1 with ⟨k,hk⟩
            simp [hk] at hodd
            absurd hodd
            apply Nat.not_odd_iff_even.mpr (by simp)
          · exact h32
        -- therefore p ∣ x^2+x
        have hh3: p ∣ (x^2+x).toNat := by
          have: (x^2+x).toNat = (x.toNat)^2 + x.toNat := by
            zify; rw [Int.toNat_of_nonneg]
            simp [Int.toNat_of_nonneg x_nng]
            linarith [sq_nonneg x, x_nng]
          rw [this]
          exact Nat.dvd_add (dvd_pow hh2 (by norm_num)) hh2
        -- but p divide x^2+x+1, therefore p ∣ 1
        rw [Int.toNat_add (by nlinarith [x_nng]) (by simp)] at h1
        exact (Nat.dvd_add_iff_right hh3).mpr h1
      rw [← Int.toNat_of_nonneg nng_1, ← Int.toNat_of_nonneg nng_2]
      exact Nat.isCoprime_iff_coprime.mpr this
    -- if mul of two coprime integers is cubic,
    -- then both integers are also cubic
    have h3: ∃a b, x^2+x+1 = a^3 ∧ x^2-x+1 = b^3 := by
      have odd3: Odd 3 := by exact Nat.odd_iff.mpr rfl
      obtain ⟨⟨a,ha⟩, ⟨b,hb⟩⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd h2 odd3 heq.symm
      use a,b
    -- if x=0, easy to find y = 1
    by_cases hx: x = 0
    · have yeq: y = 1 := by
        simp [hx] at heq
        have: (1:ℤ) = 1^3 := by simp
        rw [this] at heq
        apply (pow_left_inj₀ ?_ (by norm_num) (by norm_num)).mp heq
        apply lemma_nng_of_cube_nng
        simp [heq]
      -- so (x,y) = (0,1) is a set of solution
      simp [hx, yeq]
    replace hx: x ≥ 1 := by omega
    -- and we already prove impossible for x ≥ 1
    rcases h3 with ⟨a,b,ha,hb⟩
    have not_hx := case_xge1 ha hb
    linarith [hx, not_hx]
  · -- verify x=0, y=1 satisfy the equation
    simp; intro hx hy
    simp [hx, hy]