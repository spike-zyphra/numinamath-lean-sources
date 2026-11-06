import Mathlib

theorem algebra_229 :
  IsLeast {x | ∃ l w h : ℝ, l > 0 ∧ w > 0 ∧ h > 0 ∧
  x = (l^3 + w^3 + h^3) / (l * w * h)} 3 := by
  constructor
  · -- Let l = w = h = 1
    use 1, 1, 1
    norm_num
  · -- showing minimum
    intro x hx
    rcases hx with ⟨l, w, h, hl, hw, hh, he⟩
    have h1 : l^3 + w^3 + h^3 ≥ 3 * (l * w * h) := by
      nlinarith [sq_nonneg (l - w), sq_nonneg (w - h), sq_nonneg (h - l), 
          sq_nonneg (l + w + h), sq_nonneg (l - w + h), sq_nonneg (l + w - h), sq_nonneg (-l + w + h),
          mul_pos hl hw, mul_pos hw hh, mul_pos hl hh
      ]
    have h2 : (l^3 + w^3 + h^3) / (l * w * h) ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith