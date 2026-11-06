import Mathlib

theorem number_theory_612765 (n : ℤ) (hn : n > 0) :
    (∃ a, a^3 = n^2 + 2 ∧ ∃ b, b^3 = n + 3) ↔ n = 5 := by 
  constructor 
  -- forward direction: Assume there exist integers $a$ and $b$ such that $a^3 = n^2 + 2$ and $b^3 = n + 3$
  · intro h
    obtain ⟨b, hb, a, ha⟩ := h
    have bpos : b ≥ 0 := by 
      by_contra hc
      simp at hc
      have ble : b ^ 3 < 0 := by  
        refine Odd.pow_neg ?_ hc
        unfold Odd
        use 1
        norm_num
      rw [hb] at ble
      have nge : n ^ 2 + 2 > 0 := by  
        positivity
      linarith
    have eq1 : (n + 3) ^ 2 - (n ^ 2 + 2) = 6 * n + 7 := by 
      ring_nf
    have ineq1 : a ^ 6 > b ^ 3 := by 
      have pos : 6 * n + 7 > 0 := by positivity
      rw [←eq1, ←ha, ←hb] at pos
      nlinarith
    have ineq2 : a ^ 2 > b := by 
      by_contra hc
      simp at hc
      have aux : (a ^ 2) ^ 3≤  b ^ 3 := by
        refine pow_le_pow_left₀ ?_ hc 3
        nlinarith
      nlinarith
    have ineq3 : a ^ 2 ≥ b + 1 := by nlinarith
    have ineq4 : a ^ 6 ≥ (b + 1 ) ^ 3 := by 
      have aux : (a ^ 2) ^ 3 ≥  (b + 1) ^ 3 := by 
        refine pow_le_pow_left₀ ?_ ineq3 3
        linarith
      nlinarith
    have ineq5 : 6 * n + 7 ≥ 3 * b ^ 2 + 3 * b + 1 := by 
      rw [←eq1, ←ha, ← hb] 
      nlinarith
    have ineq6 : 6 * n ≥ 3 * b ^ 2 + 3 * b - 6 := by
      nlinarith
    have ineq7 : 2 * n ≥  b ^ 2 + b - 2 := by nlinarith
    have ineq8 : 4 * b ^ 3 - 8 ≥ (b ^ 2 + b - 2 ) ^ 2 := by nlinarith
    have ineq9 : b ^ 4 - 2 * b ^ 3 - 3 * b ^ 2 - 4 * b + 12 ≤ 0:= by nlinarith
    have bbound : b ≤ 3 := by 
      nlinarith
    have bbound' : b > 1 := by 
      by_contra hc
      simp at hc
      have ble : b ^ 3 ≤ 1 ^ 3 := by 
        nlinarith
      rw [hb] at ble
      nlinarith
    interval_cases b
    -- cases b = 2
    simp_all
    have neq : n = 2 := by nlinarith
    rw [neq] at ha
    norm_num at ha
    have nsq : n ^ 2 = 6 := by linarith
    rw [neq] at nsq
    linarith
    have neq : n ^ 2 = 25 := by 
      nlinarith
    nlinarith
  -- backward direction
  · intro h
    use 3
    rw [h]
    constructor
    norm_num
    use 2
    norm_num