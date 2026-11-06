import Mathlib

/- A parametric curve is defined by
\[(x,y) = (\sin^2 t, 2 \cos t),\]where $t$ ranges over all real numbers.

The same parametric curve can be defined by
\[(x,y) = (-s^2 - 2s, 2s + 2),\]where $s$ ranges over some interval $I.$  Find the interval $I.$ -/
theorem calculus_23202 : Set.range (fun (t : ℝ) ↦ 2 * Real.cos t) = Set.range (fun (s : Set.Icc (-2) 0) ↦ 2 * s.1 + 2) := by
  ext x
  constructor
  -- If $x \in \range (2 \cos t)$, then $x \in [-2, 0]$
  intro hx
  simp only [Set.mem_range] at hx
  rcases hx with ⟨y, hy⟩
  have yin : Real.cos y - 1 ∈ Set.Icc (-2) 0 := by
    simp only [Set.mem_Icc, neg_le_sub_iff_le_add, tsub_le_iff_right, zero_add]
    constructor
    have le : -1 ≤ Real.cos y := by
      exact Real.neg_one_le_cos y
    linarith
    exact Real.cos_le_one y
  use ⟨Real.cos y - 1, yin⟩
  simp only [mul_sub, mul_one, sub_add_cancel]
  exact hy
  -- If $x \in [-2, 0], then $x \in \range (2 \cos t)$
  intro hx
  simp only [Set.mem_range, Subtype.exists, Set.mem_Icc, exists_prop] at hx
  rcases hx with ⟨a, ⟨age, ale⟩, xeq⟩ 
  have xin : x / 2 ∈ Set.range Real.cos := by
    rw [Real.range_cos]
    simp only [Set.mem_Icc]
    constructor
    linarith
    linarith
  rcases xin with ⟨t, ht⟩
  use t
  dsimp
  rw [ht]
  ring