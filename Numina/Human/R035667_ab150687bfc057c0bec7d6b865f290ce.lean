import Mathlib

theorem inequalities_309212
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    9 * a * b * c ≤ a * b + b * c + c * a ∧
    a * b + b * c + c * a ≤ (1 / 4) * (1 + 9 * a * b * c) := by
  constructor
  . calc a * b + b * c + c * a
      _ = (a + b + c) * (a * b + b * c + c * a) := by simp [hsum]
      _ = a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b ^ 2 + b * c ^ 2 + c * a ^ 2 + 3 * a * b * c := by ring
      _ ≥ 9 * a * b * c := ?_
    have h₀ : 0 ≤ (1 / 3 : ℝ) := by norm_num
    have h₁ := Real.geom_mean_le_arith_mean3_weighted h₀ h₀ h₀ (show 0 ≤ a ^ 2 * b by positivity) (show 0 ≤ b ^ 2 * c by positivity) (show 0 ≤ c ^ 2 * a by positivity) (by norm_num)
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)] at h₁
    rw [show a ^ 2 * b * (b ^ 2 * c) * (c ^ 2 * a) = (a * b * c) ^ 3 by ring] at h₁
    rw [← Real.rpow_natCast_mul (by positivity) 3] at h₁
    simp at h₁
    have h₂ := Real.geom_mean_le_arith_mean3_weighted h₀ h₀ h₀ (show 0 ≤ a * b ^ 2 by positivity) (show 0 ≤ b * c ^ 2 by positivity) (show 0 ≤ c * a ^ 2 by positivity) (by norm_num)
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)] at h₂
    rw [show a * b ^ 2 * (b * c ^ 2) * (c * a ^ 2) = (a * b * c) ^ 3 by ring] at h₂
    rw [← Real.rpow_natCast_mul (by positivity) 3] at h₂
    simp at h₂
    linarith only [h₁, h₂]
  . suffices H : a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) ≥ 0 by
      calc a * b + b * c + c * a
        _ = (a * b + b * c + c * a) * (a + b + c) := by simp [hsum]
        _ ≤ 1 / 4 * ((a + b + c) ^ 3 + 9 * a * b * c) := by linarith only [H]
        _ = 1 / 4 * (1 + 9 * a * b * c) := by simp [hsum]
    clear hsum
    wlog h : a ≥ b ∧ b ≥ c with H
    {
      rcases le_or_gt a b with h₁ | h₁
      . rcases le_or_gt b c with h₂ | h₂
        . linarith only [H c b a hc hb ha ⟨h₂, h₁⟩]
        . rcases le_or_gt c a with h₃ | h₃
          . linarith only [H b a c hb ha hc ⟨h₁, h₃⟩]
          . linarith only [H b c a hb hc ha ⟨le_of_lt h₂, le_of_lt h₃⟩]
      . rcases le_or_gt b c with h₂ | h₂
        . rcases le_or_gt a c with h₃ | h₃
          . linarith only [H c a b hc ha hb ⟨h₃, le_of_lt h₁⟩]
          . linarith only [H a c b ha hc hb ⟨le_of_lt h₃, h₂⟩]
        . linarith only [H a b c ha hb hc ⟨le_of_lt h₁, le_of_lt h₂⟩]
    }
    calc a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)
      _ = (a - b) ^ 2 * (a + b - c) + c * (a - c) * (b - c) := by ring
      _ ≥ 0 := by
        have h₁ : a + b - c ≥ 0 := by linarith
        have h₂ : a - c ≥ 0 := by linarith
        have h₃ : b - c ≥ 0 := by linarith
        positivity
