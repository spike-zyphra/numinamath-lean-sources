import Mathlib
open Set

/- The value range of the function $y=x^2-2x$ ($x \in [0, 3]$) is -/
theorem algebra_9178 : image (fun (x : ℝ) => x^2 - 2*x) (Icc 0 3) = {x | -1 ≤ x ∧ x ≤ 3} := by
  -- Let f(x) = x^2 - 2x
  let f (x : ℝ) := x^2 - 2*x
  -- f is continuous
  have fcont : Continuous f := by continuity
  -- f is antitone on [0, 1] and monotone on [1, 3]
  have ⟨h1, h2⟩ : AntitoneOn f (Icc 0 1) ∧ MonotoneOn f (Icc 1 3) := by
    constructor
    all_goals
      intro x hx y hy hxy
      simp [f] at *
      nlinarith

  -- image f [0, 1] = [f 1, f 0]
  -- By monotonicity of f on [1, 3], we have image f [1, 3] ⊆ [f 1, f 3]
  -- By continuity of f, we have image f [1, 3] ⊇ [f 1, f 3]
  replace h1 : image f (Icc 0 1) = Icc (f 1) (f 0) := by
    apply subset_antisymm
    . exact AntitoneOn.image_Icc_subset h1
    . exact intermediate_value_Icc' (by linarith) (Continuous.continuousOn fcont)

  -- image f [1, 3] = [f 1, f 3]
  -- By monotonicity of f on [1, 3], we have image f [1, 3] ⊆ [f 1, f 3]
  -- By continuity of f, we have image f [1, 3] ⊇ [f 1, f 3]
  replace h2 : image f (Icc 1 3) = Icc (f 1) (f 3) := by
    apply subset_antisymm
    . exact MonotoneOn.image_Icc_subset h2
    . exact intermediate_value_Icc (by linarith) (Continuous.continuousOn fcont)

  -- [0, 3] = [0, 1] ∪ [1, 3]
  have h3 : Icc (0 : ℝ) 3 = Icc 0 1 ∪ Icc 1 3 := by simp

  -- The image of [0, 3] is the union of the images of [0, 1] and [1, 3]
  rw [h3, image_union, h1, h2]

  -- Calculate the function at the endpoints
  simp [f]
  norm_num

  -- Trivial linear arithmetic
  ext x
  simp
  intros
  constructor <;> linarith
