import Mathlib

theorem algebra_15036 : {b : ℝ | -2 ∉ Set.range (fun x : ℝ => x ^ 2 + b * x + 2)} =
    Set.Ioo (-4) 4 := by 
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor 
  · -- Assume -2 ∉ range of f, prove b ∈ (-4,4)
    intro h 
    have h1 : ∀ x : ℝ, x ^ 2 + b * x + 2 ≠ -2 := by 
      simpa using h 
    -- Show b ^ 2 < 16
    have h2 : b ^ 2 < 16 := by 
      by_contra h2
      push_neg at h2 
      -- If b ^ 2 ≥ 16, then there exists a solution
      have h3 : ∃ x : ℝ, x ^ 2 + b * x + 2 = -2 := by 
        have h4 : b ^ 2 ≥ 16 := by linarith 
        use (-b + Real.sqrt (b ^ 2 - 16)) / 2 
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 16), Real.sq_sqrt (show b ^ 2 - 16 ≥ 0 by linarith)]
      obtain ⟨x, hx⟩ := h3 
      have h1' := h1 x 
      contradiction 
    constructor
    · -- Show that -4 < b 
      nlinarith [sq_nonneg (b)]
    · -- Show that b < 4
      nlinarith [sq_nonneg (b)]
  · -- Assume b ∈ (-4,4), prove -2 ∉ range of f
    rintro ⟨hb1, hb2⟩
    have h1 : ∀ x : ℝ, x ^ 2 + b * x + 2 ≠ -2 := by
      intro x
      by_contra h_eq
      -- Show $-2$ is not in the range
      have h_eq : x ^ 2 + b * x + 2 = -2 := by 
        simpa using h_eq 
      have h_eq1 : x ^ 2 + b * x + 4 = 0 := by
        linarith 
      -- Show discriminant is negative
      have h2 : b ^ 2 < 16 := by
        nlinarith [sq_nonneg (b), sq_nonneg (b + 4), sq_nonneg (b - 4)]
      -- Show quadratic is unsatisfiable
      have h3 : (x + b / 2) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      nlinarith [sq_nonneg (x + b / 2), sq_nonneg (b ^ 2 - 16), sq_nonneg ((b + 4) * (b - 4)), h2]
    simpa using h1