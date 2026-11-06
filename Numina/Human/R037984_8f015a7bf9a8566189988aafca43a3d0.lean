import Mathlib

/- Given a function $f(x) = x^2 + ax$, if the minimum value of $f(f(x))$ is equal to the minimum value of $f(x)$, determine the range of the value $a$. -/
theorem algebra_9332 {a : ℝ} (f : ℝ → ℝ) (f_def : f = fun x => x ^ 2 + a * x) :
    (∃ y_min, (∀ x, y_min ≤ f x) ∧ (∃ x, y_min = f x) ∧ (∀ x, y_min ≤ f (f x)) ∧ (∃ x, y_min = f (f x))) ↔ a ≤ 0 ∨ a ≥ 2 := by
  -- May also use "IsLeast", but here the minimum is the same for both f(x) and f(f(x)), so the above may be more convenient.
  apply Iff.intro -- Break the iff into two implications.
  . intro ⟨y_min, ⟨f_min, f_min_exists, _, fof_min_exists⟩⟩ -- If f(x) and f(f(x)) have same minimum, then a ≤ 0 or a ≥ 2.
    have y_min_value : y_min = -a ^ 2 / 4 := by -- The minimum value of y = f(x) is -a ^ 2 / 4.
      have h₁ : y_min ≤ -a ^ 2 / 4 := by
        specialize f_min (-a / 2)
        simp only [f_def] at f_min
        ring_nf at f_min
        linarith
      have h₂ : y_min ≥ -a ^ 2 / 4 := by
        obtain ⟨x, h₃⟩ := f_min_exists
        calc
          y_min = x ^ 2 + a * x := by simp only [f_def] at h₃; assumption
          _ = (x + a / 2) ^ 2 - a ^ 2 / 4 := by ring_nf
          _ ≥ -a ^ 2 / 4 := by linarith [sq_nonneg (x + a / 2)]
      linarith
    have min_unique (x : ℝ) : f x = -a ^ 2 / 4 → x = -a / 2 := by -- The minimum of y = f(x) is unique.
      intro h
      simp only [f_def] at h
      have g : (x + a / 2) ^ 2 = 0 := by
        linarith
      field_simp at g
      linarith
    have a_ineq₁ : -a / 2 ≥ -a ^ 2 / 4 := by -- Obtain an inequality about a since f(x) = -a / 2 must have solution.
      rw [y_min_value] at fof_min_exists
      obtain ⟨x, h⟩ := fof_min_exists
      specialize min_unique (f x)
      symm at h
      apply min_unique at h
      specialize f_min x
      rw [h, y_min_value] at f_min
      exact f_min
    have a_ineq₂ : 0 ≤ a * (a - 2) := by
      ring_nf
      linarith
    rw [mul_nonneg_iff] at a_ineq₂
    obtain ⟨_, h⟩ | ⟨h, _⟩ := a_ineq₂
    . exact Or.inr (by linarith)
    . exact Or.inl (by linarith)
  . intro a_ineq₁ -- If a ≤ 0 or a ≥ 2, then there exists common minimum to f(x) and f(f(x)).
    use (-a ^ 2 / 4)
    have f_min : ∀ x, -a ^ 2 / 4 ≤ f x := by
      intro x
      simp only [f_def]
      have : (x + a / 2) ^ 2 ≥ 0 := by
        exact sq_nonneg (x + a / 2)
      ring_nf at this
      linarith
    refine ⟨? g₁, ? g₂, ? g₃, ? g₄⟩ -- Simple checking.
    . exact f_min
    . use (-a / 2)
      simp only [f_def]
      linarith
    . intro x
      apply f_min (f x)
    . use ((-a + √(a ^ 2 - 2 * a)) / 2)
      have a_ineq₂ : 0 ≤ a * (a - 2) := by
        cases a_ineq₁ with
        | inl h =>
          nlinarith
        | inr h =>
          nlinarith
      have : f ((-a + √(a ^ 2 - 2 * a)) / 2) = -a / 2 := by
        simp only [f_def]
        ring_nf
        rw [Real.sq_sqrt]
        ring_nf
        linarith
      rw [this]
      simp only [f_def]
      ring_nf
