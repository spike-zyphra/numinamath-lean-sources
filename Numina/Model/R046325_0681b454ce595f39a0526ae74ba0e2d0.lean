import Mathlib

open Real

theorem algebra_4159 {a : ℝ} (ha : 1 < a) :
  ∑' i : ℕ, 1 / a ^ (i + 1) = 1 / (a - 1) := by 
  have h1 : ∑' i : ℕ, 1 / a ^ (i + 1) = ∑' i : ℕ, (1 / a) ^ (i + 1) := by
    congr
    funext i 
    ring_nf
    <;> field_simp
  rw [h1]
  have h5 : ∑' i : ℕ, (1 / a : ℝ) ^ (i + 1) = (1 / (a - 1 : ℝ)) := by 
    have h6 : ∀ (n : ℕ), (1 / a) ^ (n + 1) = (1 / a) * ( (1 / a) ^ n ) := by
      intro n
      ring_nf 
      <;> field_simp
      <;> ring
      <;> field_simp
    have h7 : ∑' i : ℕ, ( (1 / a) ^ (i + 1) ) = ∑' i : ℕ, ( (1 / a) * ( (1 / a) ^ i ) ) := by 
      congr
      funext i
      exact h6 i
    rw [h7]
    rw [tsum_mul_left]
    have h8 : ∑' i : ℕ, ( (1 / a : ℝ) : ℝ ) ^ i = ( 1 / (1 - (1 / a : ℝ) ) ) := by 
      rw [tsum_geometric_of_norm_lt_one]
      · norm_num 
      · -- Show that |1/a| < 1 
        have h6' : (1 / a : ℝ) < 1 := by
          apply (div_lt_iff₀ (by linarith)).mpr
          linarith 
        have h6'' : norm ( (1 / a : ℝ) ) < 1 := by 
          rw [norm_eq_abs]
          apply abs_lt.mpr 
          constructor
          · -- Show that -1 < 1/a. But 1/a is positive because a > 1 > 0
            have : 0 < (1 / a : ℝ) := by 
              apply one_div_pos.mpr 
              linarith 
            linarith 
          · 
            linarith [h6'] 
        simpa using h6''
    rw [h8]
    field_simp 
    <;> ring_nf <;> field_simp 
    <;> ring_nf <;> field_simp <;> tauto 
    all_goals 
      norm_num 
      <;> try { linarith } 
      all_goals tauto 
    all_goals 
      norm_num 
      <;> try { linarith } 
      all_goals tauto 
  rw [h5]
  <;> field_simp [sub_ne_zero, ne_of_gt ha]
  <;> ring_nf 
  <;> field_simp [sub_ne_zero, ne_of_gt ha]
  <;> tauto 
  all_goals 
    norm_num 
    <;> try { linarith }
    all_goals tauto 
  all_goals 
    norm_num 
    <;> try { linarith }
    all_goals tauto
  all_goals norm_num