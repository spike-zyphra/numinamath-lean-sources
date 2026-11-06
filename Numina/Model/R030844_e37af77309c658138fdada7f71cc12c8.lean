import Mathlib

theorem algebra_243379 {p q : ℝ} {m k : ℕ} (h1 : 2^m + 2^k = p) (h2 : 2^m - 2^k = q) :
    2^(m + k) = (p^2 - q^2) / 4 := by
  have h3 : (2 : ℝ) ^ m = (p + q) / 2 := by
    have eq1 : (2 : ℝ) ^ m + (2 : ℝ) ^ k = p := by
      exact_mod_cast h1
    have eq2 : (2 : ℝ) ^ m - (2 : ℝ) ^ k = q := by
      exact_mod_cast h2
    have eq3 : (2 : ℝ) ^ m = (p + q) / 2 := by
      linarith
    exact_mod_cast eq3
  have h4 : (2 : ℝ) ^ k = (p - q) / 2 := by
    have eq1 : (2 : ℝ) ^ m + (2 : ℝ) ^ k = p := by
      exact_mod_cast h1
    have eq2 : (2 : ℝ) ^ m - (2 : ℝ) ^ k = q := by
      exact_mod_cast h2
    have eq3 : (2 : ℝ) ^ k = (p - q) / 2 := by
      linarith
    exact_mod_cast eq3
  have h5 : (2 : ℝ) ^ (m + k) = (2 : ℝ) ^ m * (2 : ℝ) ^ k := by 
    rw [pow_add]
    all_goals norm_num
  rw [h5]
  rw [h3, h4]
  <;> field_simp
  <;> ring
  all_goals norm_num