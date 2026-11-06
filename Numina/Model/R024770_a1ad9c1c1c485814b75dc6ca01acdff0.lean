import Mathlib

open Real

theorem algebra_5532 : {n : ℤ | ∃ x : ℝ, n = 2018 / (101 + exp x)} = {n | 1 ≤ n ∧ n ≤ 19} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume that there exists real x such that n = 2018/(101 + exp x), then 1 ≤ n ≤ 19
    intro h
    rcases h with ⟨x, hx⟩
    have hx1 : (n : ℝ) = 2018 / (101 + exp x) := by exact_mod_cast hx
    have h1 : 0 < 101 + exp x := by
      have h2 : exp x > 0 := Real.exp_pos x
      linarith
    have h2 : 0 < (2018 : ℝ) / (101 + exp x) := by
      apply div_pos
      all_goals linarith
    have h3 : (2018 : ℝ) / (101 + exp x) < (2018 / (101 : ℝ) : ℝ) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      linarith [Real.exp_pos x]
    -- Transform the inequality to integer n
    have h4 : (n : ℝ) < (2018 / (101 : ℝ) : ℝ) := by
      rw [hx1]
      exact h3
    -- From h3: n < ~19.98, so n ≤ 19
    have h5 : n < 20 := by
      by_contra h
      push_neg at h
      have h6 : n ≥ 20 := by omega
      have h7 : (n : ℝ) ≥ (20 : ℝ) := by exact_mod_cast h6
      nlinarith [h3, Real.exp_pos x, h4, h2]
    -- From h2: n > 0
    have h6 : n ≥ 1 := by
      by_contra h
      push_neg at h
      have h7 : n ≤ 0 := by omega
      have h8 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h7
      nlinarith [h2, hx1, Real.exp_pos x]
    constructor
    · omega
    · omega
  · -- Assume n is integer with 1 ≤ n ≤ 19, then there exists real x such that n = 2018/(101 + exp x)
    rintro ⟨hn1, hn2⟩
    use Real.log ((2018 - (101 * (n : ℝ))) / (n : ℝ))
    have h4 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by omega
    have h5 : exp (Real.log ((2018 - (101 * (n : ℝ))) / (n : ℝ))) = ((2018 - (101 * (n : ℝ))) / (n : ℝ)) := by
      rw [Real.exp_log]
      have h6 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by omega
      have h6' : ((2018 - (101 * (n : ℝ))) / (n : ℝ) : ℝ) > 0 := by
        have hn2' : n ≤ 19 := by linarith
        have h9 : n ≤ 19 := by linarith
        have h9' : (n : ℝ) ≤ (19 : ℝ) := by exact_mod_cast h9
        have h6 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by omega
        have h7 : (2018 - (101 * (n : ℝ)) : ℝ) > 0 := by
          have hn1' : n ≥ 1 := by linarith
          have h9 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn1'
          nlinarith
        apply div_pos
        · linarith
        all_goals linarith
      linarith
    have hx1 : (n : ℝ) = 2018 / (101 + exp (Real.log ((2018 - (101 * (n : ℝ))) / (n : ℝ))) : ℝ) := by
      rw [h5]
      field_simp [h4]
      <;> nlinarith [Real.log_pos (show (2018 - (101 * (n : ℝ)) ) / (n : ℝ) > (1 : ℝ) by
        have hn1' : n ≥ 1 := by linarith
        have h6 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn1'
        have h7 : (2018 - (101 * (n : ℝ)) : ℝ) > 0 := by
          have hn1' : n ≥ 1 := by linarith
          have h9 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn1'
          nlinarith
        apply (div_pos (by nlinarith) (by nlinarith))
      )]
    exact_mod_cast hx1