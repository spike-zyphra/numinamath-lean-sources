import Mathlib

open Real Set
open scoped BigOperators
/-The minimum value of the function $y=\cos \left(x-\dfrac{\pi }{8}\right)$ where $x\in \left[\dfrac{\pi}{6},\dfrac{2}{3}\pi \right]$ is ______________.-/
theorem algebra_9377 (f : ℝ → ℝ) (hf : f = λ x => cos (x - π / 8)) :
    IsLeast {y | ∃ x ∈ Icc (π / 6) (2 * π / 3), f x = y} (cos (π *(13/ 24))) := by
    constructor
    -- prove the first side
    simp
    -- find the mini value
    use (π *(2/3))
    constructor
    -- use the definition
    constructor
    any_goals (ring_nf;simp [Real.pi_pos];linarith)
    -- prove the bound and proof them
    ring_nf
    simp [Real.pi_pos]
    -- replace with definition
    rw [hf]
    simp
    ring_nf

    -- prove the other side
    rw [mem_lowerBounds]
    -- translate into quantification problem
    intro x hx
    simp at hx
    -- unfold cases
    rcases hx with ⟨t,ht⟩
    -- replace x with f t
    rw [← ht.2,hf]
    simp
    -- use cos' monocity
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    linarith
    linarith
    linarith



