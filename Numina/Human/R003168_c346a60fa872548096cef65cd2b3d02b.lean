import Mathlib

/- 6. Satisfy $a \geqslant b \geqslant c$ and $a b c=2(a-1)(b-1)(c-1)$, the number of positive integer solutions $(a, b, c)$ is $\qquad$
A. 4
B. 5
C. 6
D. 7 -/
theorem number_theory_158617 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≥ b ∧ b ≥ c ∧ a * b * c = 2 * (a - 1) * (b - 1) * (c - 1)}.ncard = 5 := by
  -- we'll provide the explicit solution set, which has cardinality 5
  suffices {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≥ b ∧ b ≥ c ∧ a * b * c = 2 * (a - 1) * (b - 1) * (c - 1)} =
      {(16,5,3), (10,6,3), (8, 7, 3), (9, 4, 4), (6, 5, 4)} by
    rw [this]
    repeat rw [Set.ncard_insert_of_not_mem (by simp)]
    rw [Set.ncard_singleton]
  ext s; simp
  constructor <;> rintro h
  -- proving the equation implies one of the solutions
  . simp [Prod.ext_iff]
    set a := s.1
    set b := s.2.1
    set c := s.2.2
    obtain ⟨ha, hb, hc, hab, hbc, h⟩ := h
    -- first prove lower bound of c, as c ≤ 1 would imply rhs is 0 but lhs is positive
    have hc_lb : 2 ≤ c := by
      by_contra hc_lb
      replace hc_lb : c - 1 = 0 := by omega
      rw [hc_lb] at h
      have : 0 < a * b * c := by positivity
      rw [h] at this
      simp at this
    replace ha : 1 ≤ a := by omega
    replace hb : 1 ≤ b := by omega
    replace hc : 1 ≤ c := by omega
    -- next prove upper bound of c, 5 ≤ c implies 1/5 ≤ 1/c ≤ 1/b ≤ 1/a which then implies (1 - 1/a) * (1 - 1/b) * (1 - 1/c) is larger than 1/2
    have hc_ub : c ≤ 4 := by
      by_contra hc_ub
      replace hc_ub : 5 ≤ c := by omega
      replace h : (a : ℚ) * b * c = 2 * (a-1) * (b - 1) * (c - 1) := by
        norm_cast
      replace h : (1:ℚ)/2 = (1 - 1/a) * (1 - 1/b) * (1 - 1/c) := by
        field_simp
        linear_combination h
      have : (4 / 5 : ℚ)^3 ≤ (1 - 1/a) * (1 - 1/b) * (1 - 1/c) := by
        rw [pow_three, mul_comm]
        replace ha : (1 - 1 / 5 : ℚ) ≤ 1 - 1/a := by
          gcongr
          norm_cast
          linarith
        replace hb : (1 - 1 / 5 : ℚ) ≤ 1 - 1/b := by
          gcongr
          norm_cast
          linarith
        replace hc : (1 - 1 / 5 : ℚ) ≤ 1 - 1/c := by
          gcongr
          norm_cast
        gcongr
        . linear_combination ha
        . linear_combination hb
        . linear_combination hc
      linarith
    -- now we casework on c = 2, 3, 4
    interval_cases c <;> simp
    -- for c = 2, the equations relate a, b with a-1, b-1 impossible as one is bigger
    . have : a * b * 2 < a * b * 2 := by
        nth_rw 1 [h]
        ring_nf
        gcongr <;> omega
      simp at this
    -- for c = 3, we first note b ≠ 3, as pluggin in b = 3, we get no solution
    . have hb' : b ≠ 3 := by
        by_contra hb'
        rw [hb'] at h
        omega
      -- so b, a ≥ 4
      replace hbc : 4 ≤ b := by omega
      have hab' : 4 ≤ a := by linarith
      -- equation can be written as (a-4) * (b-4) = 12
      replace h : (a : ℤ) * b * 3 = 2 * (a - 1) * (b - 1) * (3 - 1) := by norm_cast
      replace h : (a - 4 : ℤ) * (b - 4) = 12 := by linear_combination -h
      norm_cast at h
      -- so a-4 is a divisor of 12, trying out all, we get some solutions
      have ha : (a-4) ∈ (12).divisors := by
        refine Nat.mem_divisors.mpr ?_
        simp
        use (b-4)
        rw [h]
      have : (12).divisors = {1, 2, 3, 4, 6, 12} := by decide
      rw [this] at ha
      simp at ha
      obtain ha | ha | ha | ha | ha | ha := ha <;> rw [ha] at h
      all_goals omega
      -- for c = 4, the equatin is (a-3) * (b-3) = 6
    . replace h : (a : ℚ) * b * 4 = 2 * (a - 1) * (b - 1) * (4 - 1) := by norm_cast
      replace h : (a - 3 : ℚ) * (b - 3) = 6 := by linear_combination -h / 2
      replace hbc' : 3 ≤ b := by linarith
      replace hab' : 3 ≤ a := by linarith
      norm_cast at h
      -- trying out a-3 as disisor of 6, we get some solutions
      have ha : (a-3) ∈ (6).divisors := by
        refine Nat.mem_divisors.mpr ?_
        simp
        use (b-3)
        rw [h]
      have : (6).divisors = {1, 2, 3, 6} := by decide
      rw [this] at ha
      simp at ha
      obtain ha | ha | ha | ha := ha <;> rw [ha] at h
      all_goals omega
  -- to prove solutsion satisfy equation, just plug in and prove
  . obtain rfl | rfl | rfl | rfl | rfl := h
    all_goals simp