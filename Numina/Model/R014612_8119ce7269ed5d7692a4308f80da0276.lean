import Mathlib

theorem inequalities_128511 (a b c d h k : ℝ) (h₀ : 0 < d) (h₁ : d < c) (h₂ : c < b)
    (h₃ : b < a) (h₄ : ∃ r : ℝ, 0 < r ∧ a = b + r ∧ b = c + r ∧ c = d + r)
    (h₅ : ∃ r : ℝ, 0 < r ∧ a = h * r ∧ h = k * r ∧ k = d * r) :
    b * c > h * k := by
  rcases h₄ with ⟨r, hr₀, ha₁, hb₁, hc₁⟩
  rcases h₅ with ⟨s, hs₀, ha₂, hb₂, hk₂⟩
  have ha3 : a = d + 3 * r := by
    nlinarith [hc₁, hb₁, ha₁]
  have ha4 : a = d * s ^ 3 := by
    have hk₃ : k = d * s := by linarith [hk₂]
    have hb₃ : h = k * s := by linarith [hb₂]
    rw [hk₃] at hb₃
    have ha₃ : a = h * s := by linarith [ha₂]
    rw [hb₃] at ha₃
    nlinarith
  have hb2 : b = d + 2 * r := by
    nlinarith [hb₁, hc₁]
  have hc2 : c = d + r := by
    linarith [hc₁]
  have ha5 : h * k = d ^ 2 * s ^ 3 := by
    have hk₃ : k = d * s := by linarith [hk₂]
    have hb₃ : h = d * s ^ 2 := by
      have hb₄ : h = k * s := by linarith [hb₂]
      rw [hb₄]
      rw [hk₃]
      <;> nlinarith
    rw [hb₃, hk₃]
    nlinarith
  -- Compute h * k
  have ha6 : h * k = d ^ 2 + 3 * r * d := by
    have eq1 : d * s ^ 3 = d + 3 * r := by 
      nlinarith [ha3, ha4]
    have eq2 : h * k = d ^ 2 * s ^ 3 := by
      nlinarith [ha5]
    calc
      h * k = d ^ 2 * s ^ 3 := by linarith [eq2]
      _ = d * (d * s ^ 3) := by ring
      _ = d * (d + 3 * r) := by rw [eq1]
      _ = d ^ 2 + 3 * r * d := by ring
  -- Compute b * c
  have ha7 : b * c = d^2 + 3 * r * d + 2 * r^2 := by
    rw [hb2, hc2]
    nlinarith
  nlinarith [ha6, ha7, hr₀]