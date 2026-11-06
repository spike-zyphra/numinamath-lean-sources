import Mathlib

open Real

theorem inequalities_27739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 = b^2 + c^2) (h1 : a > b) (h2 : a > c) :
    {x | a^x > b^x + c^x} = {x | x > 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume a^x > b^x + c^x, prove x > 2
    intro h1'
    by_contra h
    push_neg at h
    have h3 : x ≤ 2 := by
      omega
    have h4 : x = 0 ∨ x = 1 ∨ x = 2 := by 
      omega
    rcases h4 with (h4 | h4 | h4)
    · -- Case x = 0
      rw [h4] at h1'
      norm_num at h1'
      all_goals linarith
    · -- Case x = 1
      rw [h4] at h1'
      norm_num at h1'
      all_goals nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Case x = 2
      rw [h4] at h1'
      all_goals nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  · -- Assume x > 2, prove a^x > b^x + c^x
    intro h
    have h3 : x > (2 : ℕ) := by
      omega
    have h4 : a ^ x > b ^ x + c ^ x := by
      have h5 : x ≥ 3 := by 
        omega
      have h6 : a > 0 := by linarith
      have h7 : b > 0 := by linarith
      have h8 : c > 0 := by linarith
      have h9 : ∀ (n : ℕ), n ≥ 3 → a ^ n > b ^ n + c ^ n := by
        intro n hn
        have h10 : n ≥ 3 := hn
        have h11 : a ^ 3 > b ^ 3 + c ^ 3 := by
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
            h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            h1, h2, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)]
        have h12 : ∀ (k : ℕ), k ≥ 3 → a ^ k > b ^ k + c ^ k → a ^ (k + 1) > b ^ (k + 1) + c ^ (k + 1) := by
          intro k hk h14
          have h15 : a ^ (k + 1) = a * a ^ k := by ring
          have h16 : b ^ (k + 1) = b * b ^ k := by ring
          have h17 : c ^ (k + 1) = c * c ^ k := by ring
          rw [h15, h16, h17]
          nlinarith [h1, h2, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h14, pow_pos ha k, pow_pos hb k, pow_pos hc k]
        exact Nat.le_induction h11 h12 n h10
      specialize h9 x (by omega)
      simpa using h9
    simpa using h4