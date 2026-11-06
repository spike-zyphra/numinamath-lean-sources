import Mathlib

theorem algebra_185395 (x : ℝ) (hx : x ≠ 1 ∧ x ≠ -1) :
    x / (x ^ 2 - 1) = 1 / (2 * (x + 1)) + 1 / (2 * (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by 
    intro h
    apply hx.1
    linarith 

  have h2 : x + 1 ≠ 0 := by 
    intro h
    apply hx.2
    linarith 

  have h3 : x ^ 2 - 1 ≠ 0 := by 
    by_contra h
    have h4 : (x - 1) * (x + 1) = 0 := by 
      linarith [h]
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- x - 1 = 0 
      exfalso 
      have h5' : x = 1 := by linarith 
      rw [h5'] at hx 
      contradiction 
    · -- x + 1 = 0 
      exfalso 
      have h6' : x = -1 := by linarith 
      rw [h6'] at hx 
      contradiction 
  -- Remove denominators and clear denominators
  field_simp [(show x ^ 2 - 1 ≠ 0 by assumption), (show x - 1 ≠ 0 by assumption), (show x + 1 ≠ 0 by assumption)]
  <;> ring_nf 
  <;> field_simp [(show x ^ 2 - 1 ≠ 0 by assumption), (show x - 1 ≠ 0 by assumption), (show x + 1 ≠ 0 by assumption)]
  <;> nlinarith 
  all_goals try { 
    try field_simp [(show x ^ 2 - 1 ≠ 0 by assumption), (show x - 1 ≠ 0 by assumption), (show x + 1 ≠ 0 by assumption)]
    all_goals try ring_nf 
    all_goals try { nlinarith }
    all_goals try { 
      exfalso 
      <;> try { 
        have h : x = 1 := by nlinarith 
        rw [h] at hx 
        contradiction 
      } <;> try { 
          have h : x = -1 := by nlinarith 
          rw [h] at hx 
          contradiction 
        }
    }
  }
  all_goals try { 
    tauto 
  }