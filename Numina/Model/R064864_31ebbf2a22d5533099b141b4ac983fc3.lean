import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_98553 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (h : a * b * c ≠ 0) :
  a / abs a + b / abs b + c / abs c + (a * b * c) / abs (a * b * c) = -4 ∨
  a / abs a + b / abs b + c / abs c + (a * b * c) / abs (a * b * c) = 0 ∨
  a / abs a + b / abs b + c / abs c + (a * b * c) / abs (a * b * c) = 4 := by
  have h1 : abs (a * b * c) = abs a * abs b * abs c := by
    simp [abs_mul]
  have h2 : (a * b * c) / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    field_simp [h1, mul_ne_zero (mul_ne_zero ha hb) hc]
    <;> ring_nf <;> norm_num
  have ha1 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h_nonneg =>
      -- If 0 ≤ a, then |a| = a, so a / |a| = 1
      have h_abs : abs a = a := abs_of_nonneg (show (0 : ℝ) ≤ a by linarith)
      left
      field_simp [h_abs, show a ≠ 0 by exact ha]
      all_goals linarith
    | inr h_neg =>
      -- If a < 0, then |a| = -a, so a / |a| = -1
      have h_abs : abs a = -a := abs_of_neg (show a < (0 : ℝ) by linarith)
      right
      field_simp [h_abs, show a ≠ 0 by exact ha]
      all_goals linarith
  have hb1 : b / abs b = 1 ∨ b / abs b = -1 := by
    cases (le_or_lt 0 b) with
    | inl h_nonneg =>
      -- If 0 ≤ b, then |b| = b, so b / |b| = 1
      have h_abs : abs b = b := abs_of_nonneg (show (0 : ℝ) ≤ b by linarith)
      left
      field_simp [h_abs, show b ≠ 0 by exact hb]
      all_goals linarith
    | inr h_neg =>
      -- If b < 0, then |b| = -b, so b / |b| = -1
      have h_abs : abs b = -b := abs_of_neg (show b < (0 : ℝ) by linarith)
      right
      field_simp [h_abs, show b ≠ 0 by exact hb]
      all_goals linarith
  have hc1 : c / abs c = 1 ∨ c / abs c = -1 := by
    cases (le_or_lt 0 c) with
    | inl h_nonneg =>
      -- If 0 ≤ c, then |c| = c, so c / |c| = 1
      have h_abs : abs c = c := abs_of_nonneg (show (0 : ℝ) ≤ c by linarith)
      left
      field_simp [h_abs, show c ≠ 0 by exact hc]
      all_goals linarith
    | inr h_neg =>
      -- If c < 0, then |c| = -c, so c / |c| = -1
      have h_abs : abs c = -c := abs_of_neg (show c < (0 : ℝ) by linarith)
      right
      field_simp [h_abs, show c ≠ 0 by exact hc]
      all_goals linarith
  rw [h2]
  rcases ha1 with haa | haa <;> rcases hb1 with hbb | hbb <;> rcases hc1 with hcc | hcc
  <;> norm_num [haa, hbb, hcc] <;> tauto