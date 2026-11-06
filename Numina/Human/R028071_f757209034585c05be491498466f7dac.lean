import Mathlib

theorem algebra_10592 : IsGreatest {x + 1 / x | (x : ℝ) (_ : x ≠ 0) (_ : x ^ 2 + 1 / x ^ 2 = 7)} 3 := by
  have H {x : ℝ} (hx : x ≠ 0) : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
    field_simp
    ring
  constructor
  . use (3 + √5) / 2
    have h₀ : (3 + √5) / 2 ≠ 0 := by positivity
    simp [h₀, H h₀, -one_div]
    suffices H : (3 + √5) / 2 + 1 / ((3 + √5) / 2) = 3 by rw [H]; norm_num
    field_simp
    ring_nf
    simp
    ring
  . rintro z ⟨x, h₁, h₂, rfl⟩
    rw [H h₁] at h₂
    nlinarith
