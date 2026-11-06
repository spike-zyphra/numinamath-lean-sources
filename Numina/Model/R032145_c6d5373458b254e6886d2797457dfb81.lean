import Mathlib

theorem algebra_9081 {f : ℝ → ℝ} (hper : Function.Periodic f 4)
    (hf : ∀ x ∈ Set.Ico 0 4, f x = x) :
    f 7.6 = 3.6 := by
  have h1 : f 7.6 = f 3.6 := by
    rw [←hper 3.6]
    norm_num
  have h2 : f 3.6 = 3.6 := by
    apply hf
    constructor
    · norm_num
    · norm_num
  rw [h1, h2]