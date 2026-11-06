import Mathlib

theorem algebra_8449 :
    {f : ℝ → ℝ | ∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2)} = {f | ∃ c, ∀ x, f x = x ^ 3 + c * x} := by 
  ext f 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume f satisfies the equation, prove f(x) = x^3 + c*x
    intro h_eq
    have h_f0 : f 0 = 0 := by
      specialize h_eq 1 1
      norm_num at h_eq 
      linarith

    use (f 1 - 1)
    intro x 
    -- We need to show $f(x) = x^3 + c \cdot x$ for all $x$.
    -- We will substitute $x = (x + 1)/2, y = (x - 1)/2$ into the functional equation.
    -- This substitution leads to $1 \cdot f(x) - x \cdot f(1) = x(x^2 - 1)$.
    -- Rearranged: $f(x) = x(x^2 - 1) + x \cdot f(1) = x^3 + (f(1) - 1)x$.
    have eq3 := h_eq ((x + 1) / 2) ((x - 1) / 2)
    have eq4 : (( (x + 1) / 2 ) - ( (x - 1) / 2 )) * f (( (x + 1) / 2 + (x - 1) / 2 )) - (( (x + 1) / 2 ) + ( (x - 1) / 2 )) * f (( (x + 1) / 2 - (x - 1) / 2 )) = 4 * (( (x + 1) / 2 )) * (( (x - 1) / 2 )) * (( ( (x + 1) / 2 ) ) ^ 2 - (( (x - 1) / 2 ) ) ^ 2 ) := by
      simpa using eq3
    have eq5 : (( (x + 1) / 2 ) - ( (x - 1) / 2 )) * f (( (x + 1) / 2 + (x - 1) / 2 )) - (( (x + 1) / 2 ) + ( (x - 1) / 2 )) * f (( (x + 1) / 2 - (x - 1) / 2 )) = 1 * f x - x * f 1 := by
      have eq1 : ( (x + 1) / 2 + (x - 1) / 2 ) = x := by ring
      have eq2 : ( (x + 1) / 2 - (x - 1) / 2 ) = 1 := by ring
      rw [eq1, eq2]
      <;> ring
    have eq6 : 1 * f x - x * f 1 = x * 1 * (x ^ 2 - 1) := by 
      have eq7 : 1 * f x - x * f 1 = x * 1 * (x ^ 2 - 1) := by
        have eq8 : (( (x + 1) / 2 ) - ( (x - 1) / 2 )) * f (( (x + 1) / 2 + (x - 1) / 2 )) - (( (x + 1) / 2 ) + ( (x - 1) / 2 )) * f (( (x + 1) / 2 - (x - 1) / 2 )) = 1 * f x - x * f 1 := by
          have eq1 : ( (x + 1) / 2 + (x - 1) / 2 ) = x := by ring
          have eq2 : ( (x + 1) / 2 - (x - 1) / 2 ) = 1 := by ring
          rw [eq1, eq2]
          <;> ring
        have eq9 : 4 * (( (x + 1) / 2 ) ) * (( (x - 1) / 2 ) ) * (( ( (x + 1) / 2 ) ) ^ 2 - (( (x - 1) / 2 ) ) ^ 2 ) = x * 1 * (x ^ 2 - 1) := by
          ring_nf
        linarith [eq8, eq9]
      linarith
    have eq10 : f x = x ^ 3 + (f 1 - 1) * x := by 
      linarith [eq6]
    simpa using eq10
  · -- Show that if f(x) = x^3 + c*x, then it satisfies the equation
    rintro ⟨c, h_eq⟩
    intro x y
    have h1 : (x - y) * (f (x + y) ) - (x + y) * (f (x - y) ) = 4 * x * y * (x ^ 2 - y ^ 2) := by
      rw [show f (x + y) = (x + y) ^ 3 + c * (x + y) by
        apply h_eq
      , show f (x - y) = (x - y) ^ 3 + c * (x - y) by
        apply h_eq
      ]
      ring_nf
    simpa using h1