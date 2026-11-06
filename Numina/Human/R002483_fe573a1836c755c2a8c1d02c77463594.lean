import Mathlib

namespace number_theory_94043

def is_geometric (n : ℕ) :=
  n ∈ Finset.Icc 100 999 ∧
  ∃ a b c, n = 100 * a + 10 * b + c ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a
    ∧ a < 10 ∧ b < 10 ∧ c < 10
    ∧ ∃ (r : ℝ), b = a * r ∧ c = b * r

end number_theory_94043

open number_theory_94043

/- Call a 3-digit number geometric if it has
3 distinct digits which, when read from left to right, form a geometric sequence.
Find the difference between the largest and smallest geometric numbers. -/
theorem number_theory_94043 (a b : ℕ) (ha : IsGreatest {n | is_geometric n} a) (hb : IsLeast {n | is_geometric n} b) : a - b = 840 := by
  -- it is enough to show that the largest geometric number is 964 and
  -- the smallest geometric number is 124
  suffices IsGreatest {n | is_geometric n} 964 ∧ IsLeast {n | is_geometric n} 124 by
    rw [IsGreatest.unique ha this.1, IsLeast.unique hb this.2]
  constructor
  -- show that 964 is the largest 3-digit geometric number
  · simp only [IsGreatest, is_geometric, Finset.mem_Icc, ne_eq, Set.mem_setOf_eq, Nat.reduceLeDiff,
    and_self, true_and, upperBounds, and_imp, forall_exists_index]
    constructor
    -- show that 964 is a 3-digit geometric number
    · use 9, 6, 4
      norm_num
      use 2 / 3
      norm_num
    -- show that 964 is larger than any other 3-digit geometric number
    · intro n hn1 hn2 a b c hn_eq hab hbc hca h10 hb10 hc10 r
      -- consider 2 cases: a < 9 or a = 9
      rcases show a < 9 ∨ a = 9 by omega with ha | ha
      -- if a < 9 then n < 900 < 964
      · omega
      · rw [ha]; intro hbr hcr
        have hr : r = b / 9 := by simp [hbr]
        rcases show b < 6 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 by omega with hb | hb | hb | hb | hb
        -- if b < 6 then n < 960 < 964
        · omega
        -- if b = 6 then c = 4 and n = 964 ≤ 964
        · rw [hn_eq]
          rify
          rw [hcr, hr, hb, ha]
          norm_num
        -- if b = 7 then r = 7 / 9 and c = 49 / 9 ∉ ℕ
        · contrapose! hcr
          rw [hbr, hr, hb]
          norm_num
          intro heq
          have : 9 * c = 49 := by rify; linarith
          omega
        -- if b = 8 then r = 8 / 9 and c = 64 / 9 ∉ ℕ
        · contrapose! hcr
          rw [hbr, hr, hb]
          norm_num
          intro heq
          have : 9 * c = 64 := by rify; linarith
          omega
        -- if b = 9 then b = a: a contradicition with a ≠ b
        · omega
  -- show that 124 is the smallest 3-digit geometric number
  · simp only [IsLeast, is_geometric, Finset.mem_Icc, ne_eq, Set.mem_setOf_eq, Nat.reduceLeDiff,
    and_self, true_and, lowerBounds, and_imp, forall_exists_index]
    constructor
    -- show that 124 is a 3-digit geometric number
    · use 1, 2, 4; norm_num
    -- show that 124 is smaller than any other 3-digit geometric number
    · intro n hn1 hn2 a b c hn_eq hab hbc hca ha10 hb10 hc10 r
      -- consider 3 cases: a = 0 or a = 1 or a > 1
      rcases show a = 0 ∨ a = 1 ∨ a > 1 by omega with ha | ha | ha
      -- if a = 0 then n < 100: a contradiction with 100 ≤ n
      · omega
      -- if a = 1 then b = r. Consider 4 cases: b = 0 or b = 1 or b = 2 or b > 2
      · simp [ha]; intro hbr hcr
        rcases show b = 0 ∨ b = 1 ∨ b = 2 ∨ b > 2 by omega with hb | hb | hb | hb
        -- if b = 0 then r = 0 and c = 0: a contradiction with b ≠ c
        · contrapose! hbc
          rify
          simp [hcr, ←hbr, hb]
        -- if b = 1 then b = a: a contradiction with a ≠ b
        · omega
        -- if b = 2 then c = b * r = b * b = 4, 124 ≤ 124
        · rify
          simp [hn_eq, ha, hcr, ←hbr, hb]
          norm_num
        -- if b > 2 then n > 124
        · omega
      -- if a > 1 then n ≥ 200
      · omega