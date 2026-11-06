import Mathlib

theorem inequalities_219197 (f : ℝ → ℝ) :
    (∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + 3 * z)) ↔
    ∃ c, ∀ x, f x = c := by
  constructor
  · -- First, we show the inequality implies f is constant
    intro h
    have h1 : ∀ t : ℝ, f t ≤ f 0 := by
      intro t
      have h2 := h t 0 0
      have eq3 : f (t + (0 : ℝ)) + f (0 + (0 : ℝ)) + f ((0 : ℝ) + t) ≥ 3 * f (t + 2 * (0 : ℝ) + 3 * (0 : ℝ)) := by
        simpa using h2 
      have eq4 : f t + f 0 + f t ≥ 3 * f t := by 
        ring_nf at eq3 ⊢ 
        linarith 
      linarith 
    -- Now show f t >= f 0
    have h2 : ∀ t : ℝ, f t ≥ f 0 := by 
      intro t 
      have h3 := h t (-t / 2) 0
      have eq3 : f (t + (-t / 2 : ℝ)) + f ((-t / 2 : ℝ) + (0 : ℝ)) + f ((0 : ℝ) + t) ≥ 3 * f (t + 2 * (-t / 2) + 3 * (0 : ℝ)) := by 
        simpa using h3 
      have eq4 : f (t / 2) + f (-t / 2) + f t ≥ 3 * f 0 := by
        ring_nf at eq3 ⊢ 
        linarith 
      -- Now, use h1 to know that f(t/2) ≤ f(0) and f(-t/2) ≤ f(0)
      have h3' : f (t / 2) ≤ f 0 := by 
        specialize h1 (t / 2) 
        linarith 
      have h4' : f (-t / 2) ≤ f 0 := by 
        specialize h1 (-t / 2) 
        linarith 
      linarith [eq4, h3', h4'] 
    -- Now f(t) = f(0) 
    use f 0 
    intro x 
    have h3 := h1 x 
    have h4 := h2 x 
    linarith 
  · -- Now the reverse 
    rintro ⟨c, hc⟩ 
    intro x y z 
    simp [hc]
    <;> ring_nf
    <;> norm_num 
    <;> linarith 
    all_goals linarith