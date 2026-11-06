import Mathlib

theorem algebra_13911 : {z : ℝ | ∃ f : ℝ → ℝ, (∀ x y, f (x + y) = f x * f y) ∧ f 0 = z} = {0, 1} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume there exists f such that ∀ x y, f (x + y) = f x * f y and f 0 = z
    intro h
    rcases h with ⟨f, hf, hf0⟩
    have h1 : f 0 = z := hf0
    have h2 := hf 0 0
    norm_num at h2
    rw [h1] at h2
    have h3 : z ^ 2 = z := by linarith 
    have h4 : z * (z - 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h4) with h5 h6 
    · -- h5 : z = 0 
      left
      linarith 
    · -- h6 : z - 1 = 0 
      right
      linarith 
  · -- Now prove the reverse: if z ∈ {0, 1}, then there exists f with the properties
    rintro (h | h)
    · -- z = 0 
      use fun x => (0 : ℝ)
      constructor 
      · -- Verify functional equation
        intro x y 
        simp 
      · -- Set f(0) = z 
        simp [h]
    · -- z = 1 
      use fun x => (1 : ℝ)
      constructor 
      · -- Verify functional equation
        intro x y 
        simp 
      · -- Set f(0) = z 
        simp [h]