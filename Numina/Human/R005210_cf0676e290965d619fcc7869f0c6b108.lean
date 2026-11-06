import Mathlib

/- Trouver toutes les fonctions $f$ de $\mathbb{R}$ dans $\mathbb{R}$ telles que $f(a b)=f(a+b)$ pour tous nombres irrationnels $a$ et $b$.-/
theorem algebra_606297 :
  {f: ℝ → ℝ | ∀ a: ℝ, ∀ b: ℝ, Irrational a → Irrational b → f (a * b) = f (a + b)} = {f | ∃ c, f = fun _ => c} := by
  rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
  -- It checks if the function $f$ is a constant function, then it satisfies the condition
  simp
  intro f hf
  -- Consider negative irrational number $a$, set $(√(-a), -√(-a))$ in `hf`, we got $f(a) = f(0)$
  have hf_neg {a: ℝ} (irrat_a: Irrational a) (ha: a < 0): f (a) = f 0 := by
    have a_sqrt_sq: √(-a) * √(-a) = -a := by
      rw [<-sq, Real.sq_sqrt]
      simp [irrat_a]
      linarith
    -- If $a$ is irrational, then $\sqrt{-a}$ is irrational
    have irrat_sqrt_neg_a: Irrational (√(-a)) := by
      apply Irrational.of_mul_self
      rw [a_sqrt_sq]
      simp [irrat_a]
    have h1 := hf (√(-a)) (-√(-a)) irrat_sqrt_neg_a (Irrational.neg irrat_sqrt_neg_a)
    simp [a_sqrt_sq] at h1
    exact h1
  -- Consider positive irrational number $a$, set $(-√(-a), -√(-a))$ in `hf`, we got $f(a) =  f(-2√a)$
  -- Also, $-2√a$ is a negative irrational number, so $f(a) = f(0)$
  have hf_pos {a: ℝ} (irrat_a: Irrational a) (ha: 0 < a): f (a) = f 0 := by
    have a_sqrt_sq: √a * √a = a := by rw [<-sq, Real.sq_sqrt (le_of_lt ha)]
    have irrat_sqrt_a: Irrational (-√a) := by
      apply Irrational.of_mul_self
      simp
      rw [a_sqrt_sq]
      simp [irrat_a]
    have h1 := hf (-√a) (-√a) irrat_sqrt_a irrat_sqrt_a
    simp [a_sqrt_sq] at h1
    have right_neg: -√a + -√a < 0 := by
      apply add_neg
      all_goals
        simp
        exact ha
    have right_irrat : Irrational (-√a + -√a) := by
      rw [show -√a + -√a = (-2:ℤ) * √a by ring]
      apply Irrational.int_mul
      exact Irrational.of_neg irrat_sqrt_a
      norm_num
    have := hf_neg right_irrat right_neg
    rw [this] at h1
    exact h1
  -- In conclusion, $f(a) = f(0)$ for all irrational number $a$
  have hf_irrat {a: ℝ} (irrat_a: Irrational a): f a = f 0 := by
    by_cases h: a < 0
    exact hf_neg irrat_a h
    by_cases h': a = 0
    rw [h']
    have : 0 < a := by simp at h h'; exact lt_of_le_of_ne h (Ne.symm h')
    exact hf_pos irrat_a this
  -- Consider rational number $a$, set $(a - \sqrt 2, \sqrt 2)$ in `hf`, we got $f(a) = f(\sqrt 2 (a - \sqrt 2))$
  -- Also, $\sqrt 2 (a - \sqrt 2)$ is an irrational number, so $f(a) = f(0)$
  have hf_rat {a: ℝ} (not_irrat_a: ¬Irrational a): f a = f 0 := by
    unfold Irrational at not_irrat_a
    simp at not_irrat_a
    obtain ⟨a', ha'⟩ := not_irrat_a
    rw [<-ha']
    by_cases h: a' = 0
    . rw [h]
      simp
    . rw [show a' = a' - Real.sqrt 2 + Real.sqrt 2 by ring]
      have irrat_a': Irrational (a' - Real.sqrt 2) := by simp [irrational_sqrt_two]
      rw [<-hf (a' - Real.sqrt 2) (Real.sqrt 2) irrat_a' irrational_sqrt_two]
      rw [sub_mul, <-sq, Real.sq_sqrt (by norm_num)]
      apply hf_irrat
      rw [show (2:ℝ) = (2:ℕ) by norm_num]
      apply Irrational.sub_nat
      simp [h, irrational_sqrt_two]
  -- In conclusion, $f(a) = f(0)$ for all real number $a$
  use f 0
  ext x
  by_cases h: Irrational x
  exact hf_irrat h
  exact hf_rat h
