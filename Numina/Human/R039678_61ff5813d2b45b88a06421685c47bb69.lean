import Mathlib

/- Let p and q be positive integers such that 5/9 < p/q < 4/7 and q is as small as possible. What is q - p?
(A) 7
(B) 11
(C) 13
(D) 17
(E) 19 -/
theorem number_theory_98187 :
  let Ineq (p q : ℕ) := 0 < p ∧ 0 < q ∧ (5 / 9 : ℚ) < (p / q : ℚ) ∧ (p / q : ℚ) < (4 / 7 : ℚ);
  (p q: ℕ) → (IsLeast {q : ℕ | ∃ p : ℕ, Ineq p q} q) → (Ineq p q) → q - p = 7 := by
  -- introduce all assumptions to prove q - p = 7
  rintro Ineq p q ⟨hq_in, hq_set_lb⟩ hpq
  -- break down hypothesis, in particular the inequalities
  obtain ⟨hp_pos, hq_pos, hpq_left, hpq_right⟩ := hpq
  -- we'll prove q = 16, by proving 16 is in the defined set thus q ≤ 16, and then prove 16 ≤ q
  have hq_val: q = 16 := by
    have h16_in : 16 ∈ {q : ℕ | ∃ p : ℕ, Ineq p q} := by
      use 9
      dsimp [Ineq]
      norm_num
    have hq_ub : q ≤ 16 := by exact hq_set_lb h16_in
    -- to prove 16 ≤ q, first prove 5q < 9p and 7p < 4q, which means 1 ≤ 9p-5q and 1 ≤ 4q - 7p
    have hq_lb : 16 ≤ q := by
      have hpq_left' : (5:ℚ) * q < 9 * p := by
        calc
          (5:ℚ) * q = (5:ℚ) / 9 * (q * 9) := by linarith
          _ < (p:ℚ) / q * (q * 9) := by
            refine (mul_lt_mul_iff_of_pos_right ?_).mpr hpq_left
            norm_num
            assumption
          _ = 9 * p := by field_simp; ring
      have hpq_right' : (7:ℚ) * p < 4 * q := by
        calc
          (7:ℚ) * p = p / q * (7 * q) := by field_simp; ring
          _  < 4 / 7 * (7 * q) := by
            refine (mul_lt_mul_iff_of_pos_right ?_).mpr hpq_right
            norm_num
            assumption
          _ = 4 * q := by ring
      -- via linear manipulation cancel out p to get 16 <= q
      have hpq_left' : 7 ≤ 63 * p - 35 * q := by
        norm_cast at hpq_left'
        omega
      have hpq_right' : 9 ≤ 36 * q - 63 * p := by
        norm_cast at hpq_right'
        omega
      omega
    linarith
  -- next we'll prove 9 ≤ p and p ≤ 9 by multiplying out the inequalities (which have q's value plugged in)
  have hp_lb : 9 ≤ p := by
    rw [hq_val] at hpq_left
    have hp_lb : (80:ℚ) < 9 * p := by linarith
    norm_cast at hp_lb
    omega
  have hp_ub : p ≤ 9 := by
    rw [hq_val] at hpq_right
    have hp_lb : (7:ℚ) * p < 64 := by linarith
    norm_cast at hp_lb
    omega
  -- so p = 9 and answer is trivial
  have hp_val : p = 9 := by linarith
  rw [hp_val, hq_val]