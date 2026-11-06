import Mathlib

open Real Set

/- 14. (GRE 5) Find all bases of logarithms in which a real positive number can be equal to its logarithm or prove that none exist. -/
theorem Other_483 :
  {b : ℝ | b > 0 ∧ b ≠ 1 ∧ ∃ x > 0, logb b x = x} = Ioc 0 (exp (exp (-1))) \ {1} := by
  -- We first show that the image of the function f : x ↦ log x / x is (-∞, exp (-1)].
  have H : image (fun x ↦ log x / x) (Ioi 0) = Iic (exp (-1)) := by
    ext y
    simp [image, Iic]
    constructor
    . -- First, we prove that log x / x ≤ exp (-1) for all x > 0.
      rintro ⟨x, hx, rfl⟩
      -- Set y := x / e
      let y := x * exp (-1)
      have hy : y > 0 := by positivity
      have h : x = y / exp (-1) := by simp [y]
      -- log x / x = (log y + 1) / (ey) ≤ y / ey = 1 / e
      rw [h, log_div (ne_of_gt hy) (by positivity)]
      field_simp
      have H : log y ≤ y - 1 := log_le_sub_one_of_pos hy
      suffices (log y + 1) * exp (-1) ≤ exp (-1) * y from (div_le_iff₀ hy).mpr this
      nlinarith [show exp (-1) > 0 from exp_pos (-1)]
    . -- Next, we show that every y ≤ exp (-1) is in the image of f.
      intro hy
      let f x := log x / x
      -- f is continuous on (0, ∞)
      have hf : ContinuousOn f (Ioi 0) := by
        refine ContinuousOn.div ?_ (continuousOn_id' _) (fun x hx => ne_of_gt hx)
        . refine ContinuousOn.log (continuousOn_id' _) (fun x hx => ne_of_gt hx)
      -- By the intermediate value theorem, as long as we prove that there is some x in (0, exp 1] such that f x ≤ y, we can find some x' in [x, exp 1] such that f x' = y.
      suffices ∃ a, 0 < a ∧ a ≤ exp 1 ∧ f a ≤ y by
        rcases this with ⟨a, h₁, h₂, h₃⟩
        -- Intermediate value theorem
        have H := intermediate_value_Icc h₂ (ContinuousOn.mono hf ((Icc_subset_Ioi_iff h₂).mpr h₁))
        simp [Icc, image] at H
        rcases H y h₃ (by simpa [f, ← Real.exp_neg]) with ⟨x, ⟨h₄, h₅⟩, rfl⟩
        use x, gt_of_ge_of_gt h₄ h₁
      -- Wlog, we assume -y > 0.
      wlog hy : -y > 0 with H
      {
        simp at hy
        exact ⟨1, by simp, by simp [f], by simp [f, hy]⟩
      }
      -- Set x to be the minimum of exp (-1) and 1 / (-y).
      let x := min (exp (-1)) (1 / (-y))
      -- We have x > 0.
      have hx0 : x > 0 := lt_min (by positivity) (by positivity)
      -- We have x ≤ exp (-1).
      have hx1 : x ≤ exp (-1) := min_le_left _ _
      -- We have x ≤ 1 / (-y).
      have hx2 : x ≤ 1 / (-y) := min_le_right _ _
      -- We have f x ≤ y.
      use x, hx0, inf_le_of_left_le (Real.exp_le_exp_of_le (by simp))
      simp [f]
      -- log x ≤ -1, x ≤ 1 / (-y)
      rw [div_le_iff₀' hx0]
      rw [le_div_iff₀' hy] at hx2
      calc log x
        _ ≤ -1 := (log_le_iff_le_exp hx0).mpr hx1
        _ ≤ x * y := by linarith only [hx2]

  -- The original statement clearly follows from the lemma above.
  -- Because logb b x = x ↔ log x / x = log b
  ext b
  . simp
    constructor
    . rintro ⟨h₁, h₂, x, hx, h₃⟩
      refine ⟨⟨h₁, ?_⟩, h₂⟩
      rw [logb.eq_1] at h₃
      replace h₃ : log x / x = log b := by
        field_simp [ne_of_gt h₁]
        field_simp [show log b ≠ 0 from log_ne_zero_of_pos_of_ne_one h₁ h₂] at h₃
        linear_combination h₃
      suffices log b ≤ exp (-1) from (log_le_iff_le_exp h₁).mp this
      rw [← h₃]
      apply_fun (log x / x ∈ ·) at H
      simp [image, Iic] at H
      rw [← H]
      exact ⟨x, hx, rfl⟩
    . rintro ⟨⟨h₁, h₂⟩, h₃⟩
      refine ⟨h₁, h₃, ?_⟩
      apply_fun (log b ∈ ·) at H
      simp [image, Iic] at H
      have K : log b ≤ exp (-1) := (log_le_iff_le_exp h₁).mpr h₂
      rw [← H] at K
      rcases K with ⟨x, hx, h₄⟩
      use x, hx
      simp [logb.eq_1]
      field_simp [ne_of_gt h₁] at h₄
      rw [h₄]
      field_simp [show log b ≠ 0 from log_ne_zero_of_pos_of_ne_one h₁ h₃]
