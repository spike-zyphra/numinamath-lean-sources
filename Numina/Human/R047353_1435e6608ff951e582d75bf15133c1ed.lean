import Mathlib

/- 19. (26th Russian Mathematical Olympiad, 11th Grade, Problem 1) Find all functions \( f: \mathbf{R} \rightarrow \mathbf{R} \) that satisfy the inequality \( f(x+y) + f(y+z) + f(z+x) \geqslant 3 f(x+2y+3z) \) for all \( x, y, z \in \mathbf{R} \). -/
theorem inequalities_171125 (f : ℝ → ℝ) :
    (∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + 3 * z)) ↔
    ∃ c, ∀ x, f x = c := by
  constructor
  · -- Assume the inequality holds for all x, y, z
    intro h
    -- Apply the inequality with x=0, y=0, z=0
    have h1 := h 0 0 0
    norm_num at h1
    -- Apply the inequality with x=1, y=-1, z=0
    have h2 := h 1 (-1) 0
    norm_num at h2
    -- Apply the inequality with x=1, y=1, z=-1
    have h3 := h 1 1 (-1)
    norm_num at h3
    -- Apply the inequality with x=2, y=0, z=0
    have h4 := h 2 0 0
    norm_num at h4
    -- Apply the inequality with x=1, y=0, z=0
    have h5 := h 1 0 0
    norm_num at h5
    -- Apply the inequality with x=1, y=1, z=1
    have h6 := h 1 1 1
    norm_num at h6
    -- Apply the inequality with x=1/2, y=1/2, z=-1/2
    have h7 := h (1 / 2) (1 / 2) (-1 / 2)
    norm_num at h7
    -- Claim that f is the constant function with value f(0)
    use f 0
    intro x
    -- Apply the inequality with x=x/2, y=x/2, z=-x/2
    have h8 := h (x / 2) (x / 2) (-x / 2)
    ring_nf at h8
    -- Apply the inequality with x=x, y=0, z=0
    have h9 := h x 0 0
    ring_nf at h9
    -- Use linear arithmetic to prove f(x) = f(0)
    linarith
  · -- Now prove the reverse: if f is constant, then the inequality holds
    rintro ⟨c, hc⟩
    intro x y z
    -- Simplify using the fact that f is constant
    simp [hc]
    -- Prove the inequality using linear arithmetic
    linarith
