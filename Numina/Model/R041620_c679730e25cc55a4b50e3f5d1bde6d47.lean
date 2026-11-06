import Mathlib

theorem other_273209 (p : ℝ) (hp : p ∈ Set.Icc 0 1) (h : 60 / (80 / 100 * (1 - p)) = 20 / (15 / 100 * p)) :
    p = 0.64 := by 
  rcases hp with ⟨hp0, hp1⟩
  have hp2 : p > 0 := by
    by_contra h1
    push_neg at h1
    have h1' : p = 0 := by linarith
    rw [h1'] at h
    norm_num at h
    all_goals linarith
  have hp3 : 1 - p > 0 := by
    by_contra h1
    push_neg at h1
    have : p = 1 := by linarith
    rw [this] at h
    norm_num at h
    all_goals linarith
  field_simp [(show 80 / 100 * (1 - p) ≠ 0 by positivity), (show 15 / 100 * p ≠ 0 by positivity)] at h
  ring_nf at h
  have hp4 : p = (16 / 25 : ℝ) := by
    linarith 
  rw [hp4]
  norm_num