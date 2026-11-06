import Mathlib

theorem algebra_268278 (stefan wayne : ℕ → ℝ)
    (h₀ : stefan 2000 = 100 ∧ wayne 2000 = 10000)
    (h₁ : ∀ n, stefan (n + 1) = 2 * stefan n ∧ wayne (n + 1) = wayne n / 2) :
    IsLeast {n | 2000 < n ∧ stefan n > wayne n} 2004 := by
  constructor
  · -- Show 2004 is in the set
    constructor
    · -- Show 2000 < 2004
      norm_num
    · -- Show stefan 2004 > wayne 2004
      have h_s2000 : stefan 2000 = 100 := h₀.1
      have h_w2000 : wayne 2000 = 10000 := h₀.2
      have h_s2001 : stefan 2001 = 2 * stefan 2000 := (h₁ 2000).1
      have h_s2001' : stefan 2001 = 200 := by 
        rw [h_s2000] at h_s2001
        linarith
      have h_w2001 : wayne 2001 = wayne 2000 / 2 := (h₁ 2000).2
      have h_w2001' : wayne 2001 = 5000 := by 
        rw [h_w2000] at h_w2001
        linarith
      have h_s2002 : stefan 2002 = 2 * stefan 2001 := (h₁ 2001).1
      have h_s2002' : stefan 2002 = 400 := by 
        rw [h_s2001'] at h_s2002
        linarith
      have h_w2002 : wayne 2002 = wayne 2001 / 2 := (h₁ 2001).2
      have h_w2002' : wayne 2002 = 2500 := by 
        rw [h_w2001'] at h_w2002
        linarith
      have h_s2003 : stefan 2003 = 2 * stefan 2002 := (h₁ 2002).1
      have h_s2003' : stefan 2003 = 800 := by 
        rw [h_s2002'] at h_s2003
        linarith
      have h_w2003 : wayne 2003 = wayne 2002 / 2 := (h₁ 2002).2
      have h_w2003' : wayne 2003 = 1250 := by 
        rw [h_w2002'] at h_w2003
        linarith
      have h_s2004 : stefan 2004 = 2 * stefan 2003 := (h₁ 2003).1
      have h_s2004' : stefan 2004 = 1600 := by 
        rw [h_s2003'] at h_s2004
        linarith
      have h_w2004 : wayne 2004 = wayne 2003 / 2 := (h₁ 2003).2
      have h_w2004' : wayne 2004 = 625 := by 
        rw [h_w2003'] at h_w2004
        linarith
      rw [h_s2004', h_w2004']
      all_goals norm_num 
  · -- Show that 2004 is the least element in the set
    intro n hn
    have h1 : 2000 < n := hn.1
    have h2 : stefan n > wayne n := hn.2
    by_contra h
    push_neg at h 
    have h3 : n ≤ 2003 := by linarith
    interval_cases n <;> norm_num [h₀, h₁] at h2 <;> all_goals
      linarith