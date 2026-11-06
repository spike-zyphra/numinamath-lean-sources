import Mathlib

theorem number_theory_629264 (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : a + b + c = m) (h₂ : a * b * c = m) :
    m = 6 := by
  have h3 : a * b * c = a + b + c := by 
    nlinarith [h₁, h₂]
  have h4 : a ≤ 3 := by
    by_contra h
    push_neg at h 
    -- a > 3
    have h5 : b ≤ 3 := by
      by_contra h6
      push_neg at h6
      -- b > 3 
      have h6' : c ≤ 1 := by 
        nlinarith [h3, h, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have hc1 : c > 0 := hc
      have hc2 : c = 1 := by linarith [h6', hc1]
      rw [hc2] at h3
      nlinarith [mul_pos ha hb]
    interval_cases b <;> try { 
      omega 
    }
    all_goals 
    try { 
      have h5' : c ≤ 3 := by
        nlinarith [h3, h]
      interval_cases c <;> omega 
    }
  have h81 : b ≤ 3 := by 
    by_contra h
    push_neg at h
    -- b > 3 
    have h5 : a ≤ 3 := by
      by_contra h6
      push_neg at h6 
      have h6' : c ≤ 1 := by 
        nlinarith [h3, h, h6, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have hc1 : c > 0 := hc
      have hc2 : c = 1 := by linarith [h6', hc1]
      rw [hc2] at h3
      nlinarith [mul_pos ha hb]
    interval_cases a <;> try { 
      omega 
    }
    all_goals 
    try { 
      have h5' : c ≤ 3 := by
        nlinarith [h3, h]
      interval_cases c <;> omega 
    }
  have h40 : c ≤ 3 := by 
    by_contra h 
    push_neg at h 
    -- c > 3
    have h5 : a ≤ 3 := by 
      by_contra h6 
      push_neg at h6 
      -- a > 3 
      have h5' : b ≤ 3 := by 
        by_contra h6 
        push_neg at h6 
        -- b > 3 
        have h6' : c ≤ 1 := by 
          nlinarith [h3, h6, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have hc1 : c > 0 := hc
        have hc2 : c = 1 := by linarith [h6', hc1]
        rw [hc2] at h3
        nlinarith [mul_pos ha hb]
      interval_cases b <;> try { 
        omega 
      }
    interval_cases a <;> try { 
      omega 
    }
    all_goals 
    try { 
      have h5' : b ≤ 3 := by
        by_contra h6 
        push_neg at h6 
        -- b > 3 
        have h6' : c ≤ 1 := by 
          nlinarith [h3, h6, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have hc1 : c > 0 := hc
        have hc2 : c = 1 := by linarith [h6', hc1]
        rw [hc2] at h3
        nlinarith [mul_pos ha hb]
      interval_cases b <;> omega 
    }
  have hm : m = a + b + c := by
    omega
  have hm' : m = 6 := by 
    rw [hm]
    interval_cases a <;> interval_cases b <;> omega 
  linarith