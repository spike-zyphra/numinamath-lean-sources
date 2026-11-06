import Mathlib

/- $Example 17 Given $x+y+z \neq 0$, and $\frac{x}{y+z}=a$, $\frac{y}{z+x}=b, \frac{z}{x+y}=c$. Prove: $\frac{3 a}{1+a}, \frac{3 b}{1+b}, \frac{3 c}{1+c}$ at least one is not less than 1, and at least one is not greater than 1. -/
theorem algebra_327977 (x y z a b c : ℝ) (d1 : y+z ≠ 0) (d2 : z+x ≠ 0) (d3: x+y ≠ 0)
(h₀ : x + y + z ≠ 0) 
(h₁ : x / (y + z) = a)
(h₂ : y / (z + x) = b) (h₃ : z / (x + y) = c) :
  (3 * a / (1 + a) ≥ 1 ∨ 3 * b / (1 + b) ≥ 1 ∨ 3 * c / (1 + c) ≥ 1) ∧
  (3 * a / (1 + a) ≤ 1 ∨ 3 * b / (1 + b) ≤ 1 ∨ 3 * c / (1 + c) ≤ 1) := by

    let A := 3 * a / (1+a)
    let B := 3 * b / (1+b)
    let C := 3 * c / (1+c)

    --We prove that these 3 quantites sum up to 3.
    have eq: A + B + C = 3 := by 
      have Aeq: A = 3 * x / (x+y+z) := by
        simp [A]
        rw [← h₁]
        field_simp
        ring_nf
        field_simp
        ring_nf
      have Beq: B = 3 * y / (x+y+z) := by
        have : (z + x + y)  = x + y + z := by ring
        have : (z + x + y) ≠ 0 := by 
          by_contra h
          rw [this] at h
          contradiction
        simp [B]
        rw [← h₂]
        field_simp
        left
        ring
      have Ceq: C = 3 * z / (x+y+z) := by
        simp [C]
        rw [← h₃]
        field_simp
      simp [Aeq,Beq,Ceq]
      field_simp
      ring
    
    --Then, the claim follows trivially.
    constructor
    by_contra h
    push_neg at h
    obtain ⟨h1,h2,h3⟩ := h
    linarith
    by_contra h
    push_neg at h
    obtain ⟨h1,h2,h3⟩ := h
    linarith 