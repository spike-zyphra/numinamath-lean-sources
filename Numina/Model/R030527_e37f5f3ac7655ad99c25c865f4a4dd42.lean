import Mathlib

theorem algebra_607330 (f : ℝ → ℝ) : (∀ x y, f (f x) + f (f y) = 2 * y + f (x - y)) ↔
∀ x, f x = x := by
  constructor
  · -- Forward: functional equation implies f(x) = x
    intro h
    have eq0 : f 0 = 0 := by
      have eq1 : f (f 0) + f (f 0) = f 0 := by
        specialize h 0 0
        norm_num at h ⊢
        linarith 
      -- Substituting $(f 0, 0)$ in the main hypothesis.
      have eq3 : f (f (f 0)) = 0 := by 
        have eq4 : f (f (f 0)) + f (f 0) = f (f 0) := by 
          specialize h (f 0) 0 
          norm_num at h ⊢ 
          all_goals try linarith 
        linarith 
      -- Substituting $(f 0, f 0)$ in the main hypothesis.
      -- From substitution, $2*f(f(f 0)) = 2*f 0 + f(f 0 - f 0)$.
      -- f(f 0 - f 0) = f 0.
      -- So, $0 = 2*f 0 + f 0 = 3*f 0$. Hence $f 0=0$.
      have eq6 : f (f 0 - f 0) = f 0 := by 
        have eq7 : f 0 - f 0 = (0 : ℝ) := by 
          ring 
        have eq8 : f (f 0 - f 0) = f (0 : ℝ) := by 
          rw [eq7] 
        have eq9 : f (0 : ℝ) = f 0 := by 
          simp [show f 0 = f (0 : ℝ) by rfl] 
        rw [eq8, eq9] 
      have eq7 : f (f (f 0)) + f (f (f 0)) = 2 * (f 0) + f (f 0 - f 0) := by 
        specialize h (f 0) (f 0) 
        all_goals try simp at h ⊢ 
        all_goals try linarith 
      rw [eq6] at eq7 
      rw [eq3] at eq7 
      linarith 
    -- For any $x$, we will prove $f(f x) = x$.
    have eq2 : ∀ x : ℝ, f (f x) = x := by 
      intro x 
      -- Use $(x, x)$ substitution in the main hypothesis.
      have eq3 : f (f x) + f (f x) = 2 * x + f (x - x) := by 
        specialize h x x 
        simpa using h 
      have eq4 : f (x - x) = 0 := by 
        have eq5 : x - x = (0 : ℝ) := by 
          ring 
        rw [eq5] 
        simp [eq0] 
      rw [eq4] at eq3 
      linarith 
    intro x 
    -- Use $(x, 0)$ substitution in the main hypothesis.
    have eq3 : f (f x) + f (f 0) = f x := by 
      specialize h x 0 
      norm_num at h ⊢ 
      linarith 
    have eq5 : f (f x) = x := eq2 x 
    have eq7 : f (f 0) = 0 := by 
      simp [eq0, eq2]
    linarith [eq5, eq7, eq3] 
  · -- Reverse direction: Assume f(x) = x, prove functional equation
    intro h 
    intro x y 
    simp [h] 
    <;> ring