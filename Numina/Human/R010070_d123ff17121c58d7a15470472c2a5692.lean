import Mathlib

/-What integer $n$ satisfies $0\le n<19$ and $$-200\equiv n\pmod{19}~?$$-/
theorem number_theory_15166 : (0 ≤ n ∧ n < 19 ∧ -200 ≡ n [ZMOD 19]) ↔ n = 9 := by
-- Break "iff" and introduce assumptions
  constructor
-- Apply Int.modEq_iff_add_fac and solve for the parameter $t$
  · rintro ⟨h1, h2, h3⟩; rw [Int.modEq_iff_add_fac] at h3
    rcases h3 with ⟨t, ht⟩
    have : t = 11 := by linarith
    linarith
-- Conversely, check that $n=9$ satisfies the assumptions
  intro; simp_all; rw [Int.modEq_iff_dvd]; norm_num