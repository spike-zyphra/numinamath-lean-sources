import Mathlib

theorem algebra_147840 :
    {f : ℝ → ℝ | ∀ x, f (2002 * x - f 0) = 2002 * x ^ 2} = {(fun x => x ^ 2 / 2002), (fun x => x ^ 2 / 2002 + 2 * x + 2002)} := by 
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, we show that if $f$ satisfies the functional equation, then it's one of the solutions.
    intro h
    have eq1 : f (-f 0) = 0 := by 
      specialize h 0
      norm_num at h 
      linarith 
    have eq2 : ∀ y, f y = ((y + f 0) ^ 2) / 2002 := by 
      intro y 
      have h' : f y = 2002 * ((y + f 0) / 2002) ^ 2 := by 
        specialize h ((y + f 0) / 2002)
        have : 2002 * ((y + f 0) / 2002) - f 0 = y := by 
          ring 
        rw [this] at h 
        linarith 
      field_simp at h' ⊢ 
      <;> nlinarith 
    have eq3 : f 0 * (f 0 - 2002) = 0 := by 
      have h0 : f 0 = ( (0 + f 0) ^ 2 ) / 2002 := eq2 0
      nlinarith 
    cases' (mul_eq_zero.mp eq3) with h4 h5 
    · -- Case f 0 = 0 
      have h4' : f 0 = 0 := by linarith 
      left 
      funext y 
      specialize eq2 y 
      rw [h4'] at eq2 
      linarith 
    · -- Case f 0 - 2002 = 0 
      have h5' : f 0 = 2002 := by linarith 
      right 
      funext y 
      specialize eq2 y 
      rw [h5'] at eq2 
      nlinarith 
  · -- Show the solutions satisfy the functional equation.
    rintro (h | h)
    · -- First solution
      intro x 
      simp [h] 
      <;> ring_nf 
    · -- Second solution
      intro x 
      simp [h] 
      <;> ring_nf