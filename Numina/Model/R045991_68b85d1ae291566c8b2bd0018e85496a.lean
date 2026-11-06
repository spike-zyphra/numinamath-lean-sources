import Mathlib

theorem algebra_591 {a : ℕ → ℝ}
    (ha : ∀ i, a i = (2 / 3) ^ (i + 1) - 4 / 7 ^ i) :
    (∑' i, a i) = -8 / 3 := by
  have h1 : ∀ i : ℕ, a i = (2 / 3 : ℝ) ^ (i + 1) - 4 / 7 ^ i := ha
  have h2 : ∑' i : ℕ, a i = ∑' i : ℕ, ((2 / 3 : ℝ) ^ (i + 1) - 4 / 7 ^ i) := by
    congr
    funext i 
    exact h1 i 
  rw [h2]
  have h3 : ∑' i : ℕ, ((2 / 3 : ℝ) ^ (i + 1) - 4 / 7 ^ i) = (∑' i : ℕ, ((2 / 3 : ℝ) ^ (i + 1))) - (∑' i : ℕ, (4 / 7 ^ i : ℝ)) := by 
    rw [tsum_sub]
    all_goals
      -- Show that both series are summable 
      have h1 : Summable (fun i => (2 / 3 : ℝ) ^ (i + 1)) := by
        have : (fun i => (2 / 3 : ℝ) ^ (i + 1)) = (fun i => (2 / 3) * (2 / 3) ^ i) := by
          funext i
          ring_nf
        rw [this]
        apply Summable.mul_left 
        all_goals 
          exact summable_geometric_of_lt_one (by norm_num) (by norm_num) 
      have h2 : Summable (fun i : ℕ => (4 / 7 ^ i : ℝ)) := by
        have h2 : (fun i : ℕ => (4 / 7 ^ i : ℝ)) = (fun i : ℕ => 4 * (1 / 7) ^ i) := by 
          funext i 
          field_simp 
          <;> ring
        rw [h2]
        apply Summable.mul_left 
        all_goals
          exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
      simp_all [h1, h2]
  rw [h3]
  have h4 : (∑' i : ℕ, ((2 / 3 : ℝ) ^ (i + 1))) = 2 := by 
    have h4 : ∑' i : ℕ, ((2 / 3 : ℝ) ^ (i + 1)) = ∑' i : ℕ, ((2 / 3) * (2 / 3) ^ i) := by 
      congr
      funext i 
      ring_nf 
    rw [h4]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num 
  have h5 : (∑' i : ℕ, (4 / 7 ^ i : ℝ)) = 14 / 3 := by 
    have h5 : ∑' i : ℕ, (4 / 7 ^ i : ℝ) = ∑' i : ℕ, (4 * (1 / 7) ^ i : ℝ) := by
      congr 
      funext i 
      field_simp 
      <;> ring
    rw [h5]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num 
  rw [h4, h5]
  all_goals norm_num