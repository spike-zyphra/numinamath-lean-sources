import Mathlib

theorem algebra_131815 {a b c d : ℝ} (p : ℝ → ℝ) (hp : ∀ x, |x| ≤ 1 → |p x| ≤ 1)
    (h : p = fun x => a * x ^ 3 + b * x ^ 2 + c * x + d) :
    |a| + |b| + |c| + |d| ≤ 7 := by
  have h1 := hp 1 (by norm_num)
  simp [h] at h1
  have h2 := hp (-1) (by norm_num)
  simp [h] at h2
  have h3 := hp (0) (by norm_num)
  simp [h] at h3
  have h4 := hp (1 / 2) (by norm_num [abs_le])
  simp [h] at h4
  have h5 := hp (-1 / 2) (by norm_num [abs_le])
  simp [h] at h5
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos
  cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> cases' abs_cases c with hc hc <;> cases' abs_cases d with hd hd <;> linarith