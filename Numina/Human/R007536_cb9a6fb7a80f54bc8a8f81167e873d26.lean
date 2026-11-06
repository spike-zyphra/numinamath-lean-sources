import Mathlib

/- Find the integer $n$, $0 \le n \le 5$, such that \[n \equiv -3736 \pmod{6}.\] -/
theorem number_theory_15761 : (0 ≤ n ∧ n ≤ 5 ∧ n ≡ -3736 [ZMOD 6]) → n = 2 := by
  intro h
  -- simplify
  have h1: -3736 ≡ 2 [ZMOD 6] := by
    -- notice that 6x600=3600, 6x20=120, 3736 = 3600+120+16 = 3600+120+18-2 = 6 * (600+20+3)-2
    have ht1: -3736 = 6 * (-623) + 2 := by ring
    rw [ht1, add_comm]
    apply Int.modEq_add_fac_self
  -- therefore, we have n % 6 = 2
  have h2': n ≡ 2 [ZMOD 6] := by
    apply Int.ModEq.trans (h.right.right) h1
  have h2: n % 6 = 2 := h2'
  rw [Int.emod_def] at h2
  -- since 0 ≤ n ≤ 5, n/6 = 0 (integer divide).
  have h3: n / 6 = 0 := by
    have ht1 := h.left
    have ht2 := h.right.left
    have ht3: n< 6 := by linarith [ht2]
    apply Int.ediv_eq_zero_of_lt ht1 ht3
  -- therefore we solve n=2
  rw [h3] at h2; simp at h2
  apply h2