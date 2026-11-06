import Mathlib

theorem algebra_11530 {a : ℕ → ℝ} (h : ∀ n, (2 - a (n + 1)) * (4 + a n) = 8) (ha : a 0 = 2) :
    ∑ i in Finset.range (n + 1), (1 / a i) = 2 ^ (n + 1) - 1 - (n + 1) / 2 := by

  have eq1 : ∀ n, a (n + 1) = 2 * a n / (4 + a n) := by
    intro n 
    have h1 := h n 
    have h0 : 4 + a n ≠ 0 := by
      by_contra h2
      have : a n = -4 := by linarith
      rw [this] at h1
      nlinarith
    field_simp at h1 ⊢
    nlinarith 
  have h_pos : ∀ n : ℕ, a n > 0 := by
    intro n
    induction n with
    | zero =>
      have h1 : a 0 = 2 := ha
      rw [h1]
      all_goals norm_num
      <;> norm_num 
      <;> linarith
    | succ n ih =>
      have h1 : a (n + 1) = 2 * a n / (4 + a n) := eq1 n
      have hn_pos : a n > 0 := ih
      have hn1_pos : 4 + a n > 0 := by nlinarith
      rw [h1]
      positivity
      all_goals norm_num
      all_goals nlinarith 
  have eq2 : ∀ n, 1 / a (n + 1) = 2 * (1 / a n) + 1 / 2 := by
    intro n
    have eq1' : a (n + 1) = 2 * a n / (4 + a n) := eq1 n
    have h0 : 4 + a n > 0 := by
      have h2_pos : a n > 0 := h_pos n
      linarith
    have h1_pos : a n > 0 := h_pos n
    have h0_pos : a (n + 1) > 0 := h_pos (n + 1)
    have eq3 : 1 / a (n + 1) = (4 + a n) / (2 * a n) := by
      rw [eq1']
      field_simp [h0, h1_pos]
      <;> nlinarith
    rw [eq3]
    have eq4 : (4 + a n) / (2 * a n) = 2 * (1 / a n) + 1 / 2 := by
      have hn_pos : a n > 0 := h_pos n
      field_simp [hn_pos] at *
      <;> ring_nf <;> field_simp [hn_pos]
      <;> ring_nf 
      all_goals nlinarith
      <;> linarith
    rw [eq4]
    all_goals positivity

  have eq3 : ∀ n : ℕ, 1 / a n = 2 ^ n - 1 / 2 := by
    intro n 
    induction n with
    | zero =>
      have h1 : a 0 = 2 := ha
      rw [h1]
      norm_num 
      <;> norm_num 
      <;> linarith
    | succ n ih =>
      have h1_pos : a n > 0 := h_pos n
      have h1 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 2 := eq2 n
      rw [h1]
      rw [ih]
      field_simp
      <;> ring_nf
      <;> field_simp <;> nlinarith

  have h_eq2 : ∀ i : ℕ, 1 / a i = 2 ^ i - 1 / 2 := eq3

  have h_sum : ∀ n : ℕ, ∑ i in Finset.range (n + 1), (1 / a i) = 2 ^ (n + 1) - 1 - (n + 1) / 2 := by 
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_range_succ, ha]
      <;> norm_num [ha]
      <;> norm_num 
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have h1 : 1 / a (n + 1) = 2 ^ (n + 1) - 1 / 2 := h_eq2 (n + 1)
      rw [h1]
      field_simp
      <;> ring_nf 
      <;> field_simp
      <;> ring_nf 
      <;> nlinarith
      all_goals positivity
  specialize h_sum n
  simpa using h_sum
  all_goals simp
  all_goals nlinarith
  all_goals positivity 
  all_goals simp
  all_goals tauto
  all_goals tauto
  all_goals tauto
  all_goals tauto
  all_goals tauto
  all_goals positivity 
  <;> norm_num
  <;> nlinarith
  all_goals tauto
  all_goals positivity 
  all_goals tauto
  all_goals nlinarith