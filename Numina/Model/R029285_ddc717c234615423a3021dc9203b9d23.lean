import Mathlib

open Set Real

theorem algebra_21392 (f : ℝ → ℝ) (hf : f = fun x => 1 / (1 - x)) :
    image f {x | x ≠ 1} = {y | y ≠ 0} := by 
  ext y
  simp [hf, Set.mem_image]
  constructor
  · -- First, show that if $y \in \text{image } f(\mathbb{R} \setminus \{1\})$, then $y \neq 0$.
    rintro ⟨x, hx, rfl⟩
    have h1 : x ≠ 1 := hx
    have h1' : 1 - x ≠ 0 := by
      intro h2
      have : x = 1 := by linarith 
      tauto 
    -- Show $1/(1 - x) \neq 0$.
    have h2 : (1 / (1 - x)) ≠ 0 := by
      have h1' : 1 - x ≠ 0 := h1'
      field_simp [h1']
    simpa using h2 
  · -- Now the reverse direction.
    intro hy
    use (1 - 1 / y)
    constructor 
    · -- Show x ≠ 1
      by_contra h_eq1
      have h_eq1' : 1 - (1 / y) = 1 := by
        simpa using h_eq1
      have h_eq1'' : 1 / y = 0 := by
        linarith 
      have h_ne_zero : y ≠ 0 := hy
      have h1 : 1 / y ≠ 0 := by 
        field_simp [h_ne_zero]
      contradiction 
    · -- Show f(x) = y
      field_simp [hy]