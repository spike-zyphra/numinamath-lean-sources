import Mathlib

/- Determine the functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that:


$$

f(f(x+1)+y-1)=f(x)+y

$$
 -/
theorem algebra_117295 (f : ℝ → ℝ) (h : ∀ x y, f (f (x + 1) + y - 1) = f x + y) :
    ∀ y, f y = y := by
  -- show f is surjective
  have surj : Function.Surjective f
  · intro y
    use f (0 + 1) + (y - f 0) - 1
    rw [h]
    exact add_sub_cancel (f 0) y
  rcases surj 1 with ⟨u, hu⟩
  -- show f is affine
  have almost : ∀ y, f y = f (u - 1) + y
  · intro y
    have : y = f (u - 1 + 1) + y - 1 := by rw [sub_add_cancel, hu, add_sub_cancel_left]
    conv_lhs => rw [this]
    rw [h]
  -- show that the constant is 0 and conclude
  have : f (u - 1) = 0
  · have h1 := h (u - 1) 0
    simp [hu] at h1
    have fu1 := almost (u - 1)
    rw [←h1] at fu1
    simp at fu1
    have u1 : u = 1 := by linarith
    rw [u1] at hu
    have := almost 1
    rw [hu] at this
    simp at this
    rw [fu1, h1]
    exact this
  simp [this] at almost
  exact almost