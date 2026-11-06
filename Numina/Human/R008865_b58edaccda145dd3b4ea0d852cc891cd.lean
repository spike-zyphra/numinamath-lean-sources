import Mathlib

/-Let $m \circ n=(m+n) /(m n+4)$. Compute $((\cdots((2005 \circ 2004) \circ 2003) \circ \cdots \circ 1) \circ 0)$.-/
theorem algebra_211357 (f : ℝ → ℝ → ℝ) (hf : ∀m n, f m n = (m + n) / (m * n + 4)) (t : ℕ → ℝ)
    (ht0 : t 0 = 2005) (htk : ∀k, t (k + 1) = f (t k) (2004 - k)) : t 2005 = 1 / 12 := by
  -- show that ∀a, f a 2 = 1 / 2 (when a ≠ -2)
  have hfa2 (a : ℝ) (ha : a ≠ -2) : f a 2 = 1 / 2 := by
    rw [hf]
    replace ha : a * 2 + 4 ≠ 0 := by contrapose! ha; linarith only [ha]
    field_simp
    ring_nf
  -- show that 0 < t k when k ≤ 2004
  have ht_pos (k : ℕ) (hk : k ≤ 2004) : 0 ≤ t k := by
    -- prove by induction
    induction k with
    | zero => -- when k = 0
      rw [ht0]
      norm_num
    | succ k ih => -- when k > 0
      rw [htk]
      rw [hf]
      replace ih : 0 ≤ t k := by apply ih; linarith only [hk]
      replace hk : 0 ≤ 2004 - (k : ℝ) := by rify at hk; linarith only [hk]
      -- show the fraction is nonnegative
      apply div_nonneg
      all_goals positivity
  -- have t 2003 = f (t 2002) 2
  have htk2005 := htk 2004
  have htk2004 := htk 2003
  have htk2003 := htk 2002
  norm_num at htk2004 htk2003 htk2005
  -- show that t 2003 = 1 / 2
  replace htk2003 : t 2003 = 1 / 2 := by
    rw [htk2003]
    apply hfa2
    replace ht_pos := ht_pos 2002
    norm_num at ht_pos
    linarith only [ht_pos]
  -- show that t 2004 = 1 / 3
  rw [htk2003, hf] at htk2004
  norm_num at htk2004
  -- finally show that t 2005 = 1 / 12
  rw [htk2004, hf] at htk2005
  norm_num at htk2005
  tauto
