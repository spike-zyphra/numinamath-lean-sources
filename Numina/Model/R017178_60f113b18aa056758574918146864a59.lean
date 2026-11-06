import Mathlib

theorem algebra_304127 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc 0 1, |f x| ≤ 1)
    (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c) :
    |a| + |b| + |c| ≤ 17 := by
  have h1 := hf 0 (by norm_num)
  rw [h₀] at h1
  have h2 := hf 1 (by norm_num)
  rw [h₀] at h2
  have h3 := hf (1 / 2) (by norm_num)
  rw [h₀] at h3
  have h4 := hf (1 / 4) (by norm_num)
  rw [h₀] at h4
  have h5 := hf (3 / 4) (by norm_num)
  rw [h₀] at h5
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos
  by_cases ha : a ≥ 0
  · -- If $a \geq 0$, then $|a|=a$.
    rw [abs_of_nonneg ha]
    by_cases hb : b ≥ 0
    · -- If $b \geq 0$, then $|b|=b$.
      rw [abs_of_nonneg hb]
      by_cases hc : c ≥ 0
      · -- If $c \geq 0$, then $|c|=c$.
        rw [abs_of_nonneg hc]
        linarith
      · -- If $c < 0$, then $|c|=-c$.
        rw [abs_of_neg (lt_of_not_ge hc)]
        linarith
    · -- If $b < 0$, then $|b|=-b$.
      rw [abs_of_neg (lt_of_not_ge hb)]
      by_cases hc : c ≥ 0
      · -- If $c \geq 0$, then $|c|=c$.
        rw [abs_of_nonneg hc]
        linarith
      · -- If $c < 0$, then $|c|=-c$.
        rw [abs_of_neg (lt_of_not_ge hc)]
        linarith
  · -- If $a < 0$, then $|a|=-a$.
    rw [abs_of_neg (lt_of_not_ge ha)]
    by_cases hb : b ≥ 0
    · -- If $b \geq 0$, then $|b|=b$.
      rw [abs_of_nonneg hb]
      by_cases hc : c ≥ 0
      · -- If $c \geq 0$, then $|c|=c$.
        rw [abs_of_nonneg hc]
        linarith
      · -- If $c < 0$, then $|c|=-c$.
        rw [abs_of_neg (lt_of_not_ge hc)]
        linarith
    · -- If $b < 0$, then $|b|=-b$.
      rw [abs_of_neg (lt_of_not_ge hb)]
      by_cases hc : c ≥ 0
      · -- If $c \geq 0$, then $|c|=c$.
        rw [abs_of_nonneg hc]
        linarith
      · -- If $c < 0$, then $|c|=-c$.
        rw [abs_of_neg (lt_of_not_ge hc)]
        linarith