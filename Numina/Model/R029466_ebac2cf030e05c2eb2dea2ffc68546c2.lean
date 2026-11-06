import Mathlib

theorem number_theory_318779 (n : ℕ) (a b c : ℕ) (h₀ : 0 < n) (h₁ : n = a * b * c)
    (h₂ : a.Prime ∧ b.Prime ∧ c.Prime) (h₃ : 2 * a + 3 * b = c) (h₄ : 4 * a + c + 1 = 4 * b)
    (h₅ : n < 10000) : n = 1118 := by
  have h6 : b = 6 * a + 1 := by 
    omega

  have h7 : c = 20 * a + 3 := by
    rw [h6] at h₃
    omega

  rw [h₁] at h₀ h₅
  rw [h6, h7] at h₅
  have h8 : a ≤ 22 := by
    by_contra h
    push_neg at h
    have h9 : a * (6 * a + 1) * (20 * a + 3) ≥ 10000 := by
      have h9 : a ≥ 23 := by linarith
      have h10 : 6 * a + 1 ≥ 139 := by nlinarith
      have h11 : 20 * a + 3 ≥ 463 := by nlinarith
      have h9' : a * (6 * a + 1) ≥ 23 * 139 := by
        nlinarith [show a ≥ 23 by linarith]
      have h10' : a * (6 * a + 1) * (20 * a + 3) ≥ 23 * 139 * 463 := by
        nlinarith [h9', show 20 * a + 3 ≥ 463 by nlinarith]
      nlinarith [h10']
    nlinarith
    all_goals nlinarith
  interval_cases a <;> norm_num [h6, h7] at h₂ h₅ h₁ ⊢
    <;> try { 
      trivial 
    }
    <;> try { 
      tauto 
    }
    <;> try { 
      nlinarith 
    }
    <;> try { 
      tauto 
    }
  all_goals tauto