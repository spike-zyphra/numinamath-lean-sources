import Mathlib

theorem algebra_306349 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1) :
    |a| + |b| + |c| ≤ 3 := by

  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hm1 := h (-1) (by norm_num)
  have h12 := h (1 / 2) (by norm_num [Set.mem_Icc])
  have h12' := h (-1 / 2) (by norm_num [Set.mem_Icc])

  -- From h0: |c| ≤ 1
  cases' abs_le.mp h0 with hc1 hc2
  have hc1' : -1 ≤ c := by linarith
  have hc2' : c ≤ 1 := by linarith

  -- From h1: |a + b + c| ≤ 1
  cases' abs_le.mp h1 with h1_1 h1_2
  -- |a + b + c| <= 1 means:
  -- -1 <= a + b + c <= 1
  have h1_neg : -1 ≤ a + b + c := by linarith
  have h1_pos : a + b + c ≤ 1 := by linarith

  -- From hm1: |a - b + c| ≤ 1
  cases' abs_le.mp hm1 with hm1_1 hm1_2
  -- |a - b + c| <= 1 means:
  -- -1 <= a - b + c <= 1
  have hm1_neg : -1 ≤ a - b + c := by linarith
  have hm1_pos : a - b + c ≤ 1 := by linarith
  
  -- From h12: |a/4 + b/2 + c| ≤ 1
  cases' abs_le.mp h12 with h12_1 h12_2
  -- |-a/4 + b/2 + c| <= 1 means:
  -- -1 <= a/4 + b/2 + c <= 1
  have h12_neg : -1 ≤ a * (1 / 4) + b * (1 / 2) + c := by linarith
  have h12_pos : a * (1 / 4) + b * (1 / 2) + c ≤ 1 := by linarith
  
  -- From h12': |a/4 - b/2 + c| ≤ 1
  cases' abs_le.mp h12' with h12_1' h12_2'
  -- |-a/4 + b/2 + c| <= 1 means:
  -- -1 <= a/4 - b/2 + c <= 1
  have h12_neg' : -1 ≤ a * (1 / 4) + b * (-1 / 2) + c := by linarith
  have h12_pos' : a * (1 / 4) + b * (-1 / 2) + c ≤ 1 := by linarith
  
  -- Write all the constraints:
  -- 1. -1 ≤ c ≤ 1
  -- 2. -1 ≤ a + b + c ≤ 1
  -- 3. -1 ≤ a - b + c ≤ 1
  -- 4. -1 ≤ a/4 + b/2 + c ≤ 1
  -- 5. -1 ≤ a/4 - b/2 + c ≤ 1
  
  -- Let's derive |b| ≤ 1
  have hb1 : -1 ≤ b := by linarith
  have hb2 : b ≤ 1 := by linarith
  
  -- Let's derive |a + c| ≤ 1
  have hac1 : -1 ≤ a + c := by linarith
  have hac2 : a + c ≤ 1 := by linarith
  
  -- Also, |a| ≤ 2 since |a + c| ≤ 1 and |c| ≤ 1
  -- Similarly, using reverse triangle inequality: |a| ≤ |a + c| + |c| ≤ 1 + 1 = 2
  have ha1 : a ≤ 2 := by linarith
  have ha2 : -2 ≤ a := by linarith
  
  -- So |a|, |b|, |c| ≤ 2, 1, 1 respectively. Then |a| + |b| + |c| ≤ 2 + 1 + 1 = 4
  -- But need to carefully verify that 4 is attainable (not here, actually bound is 3).
  -- Therefore, we have to verify that our constraints prevent reaching this bound.
  
  -- From these constraints, we need to show that |a| + |b| + |c| ≤ 3
  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b ≥ 0, c ≥ 0
        linarith
      · -- a ≥ 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b < 0, c ≥ 0
        linarith
      · -- a ≥ 0, b < 0, c < 0
        linarith
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a < 0, b ≥ 0, c ≥ 0
        linarith
      · -- a < 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc hc
      · -- a < 0, b < 0, c ≥ 0
        linarith
      · -- a < 0, b < 0, c < 0
        linarith