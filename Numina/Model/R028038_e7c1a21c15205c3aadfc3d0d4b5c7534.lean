import Mathlib

open scoped BigOperators

theorem algebra_111116 {a b c : ℕ → ℝ}
  (ha : ∀ n, 0 < a n)
  (hb : ∀ n, b n = ∑ i in Finset.range n, a i)
  (hc : ∀ n, c n = ∏ i in Finset.range n, b i)
  (hsum : ∀ n, b n + c n = 1) :
  IsLeast {x | ∃ n, x = 1 / a n ∧ |x - 2011| < 1} 1980 := by
  -- For n = 0: b 0 = 0
  have h1' : b 0 = 0 := by 
    rw [hb 0]
    simp
  -- For n = 0: c 0 = 1
  have h1'' : c 0 = 1 := by
    rw [hc 0]
    simp [Finset.prod_empty]
    all_goals norm_num
  -- Check b 0 + c 0 = 1, which is indeed true
  have h1_eq : b 0 + c 0 = 1 := hsum 0
  rw [h1', h1''] at h1_eq
  all_goals norm_num at h1_eq
  -- For n = 1: b 1 = a 0
  have h2' : b 1 = a 0 := by 
    rw [hb 1]
    simp [Finset.sum_singleton]
    all_goals linarith
  -- For n = 1: c 1 = b 0, which is c 1 = 0
  have h2'' : c 1 = b 0 := by
    rw [hc 1]
    simp [Finset.prod_singleton]
    all_goals norm_num
  -- From b 1 + c 1 = 1 ⇒ a 0 + 0 = 1 ⇒ a 0 = 1
  have h3 : a 0 + b 0 = 1 := by
    have h_eq1 : b 1 + c 1 = 1 := hsum 1
    have hb1 : b 1 = a 0 := by
      rw [hb 1]
      simp [Finset.sum_singleton]
      all_goals linarith
    have hc1 : c 1 = b 0 := by 
      rw [hc 1]
      simp [Finset.prod_singleton]
      all_goals linarith
    rw [hb1, hc1] at h_eq1
    linarith
  -- We know b 0 = 0 from h1', so a 0 = 1.
  have ha0 : a 0 = 1 := by
    linarith [h3, h1']
  -- For n = 2: b 2 = a 0 + a 1
  have h3' : b 2 = a 0 + a 1 := by 
    rw [hb 2]
    simp [Finset.sum_range_succ]
    all_goals linarith
  -- For n = 2: c 2 = b 0 * b 1
  have h3'' : c 2 = b 0 * b 1 := by 
    rw [hc 2]
    simp [Finset.prod_range_succ]
    <;> norm_num
    <;> norm_num [h1']
    <;> nlinarith [h1']
  -- From b 2 + c 2 = 1 ⇒ a 0 + a 1 + 0 = 1 ⇒ a 0 + a 1 = 1
  have h3_eq : b 2 + c 2 = 1 := hsum 2
  rw [h3', h3''] at h3_eq
  rw [ha0] at h3_eq
  -- Solving gives a 1 = 0
  have ha1' : a 1 = 0 := by
    nlinarith [show b 0 = 0 by linarith [h1']]
  -- Contradicts with a 1 > 0 from ha
  have ha1 : 0 < a 1 := ha 1
  linarith [ha1', ha1]