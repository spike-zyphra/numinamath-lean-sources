import Mathlib

theorem functional_equation_4187 (f: ℝ → ℝ) : (∀ x > 0, f x > 0) → (∀ x > 0, ∀ y > 0, f (x * (f y)) = y * (f x)) → (∀ε>0, ∃t:ℝ, ∀x > t, f x < ε) → ∀ x > 0, f x = x⁻¹ := by
  -- introducing assumptions
  intro hp
  intro hq
  intro hl

  -- show that 1 is fixed point
  have h₁ : f 1 = 1 := by
    have hp₁ : f 1 > 0 := hp 1 (by norm_num)
    have h' := hq 1 (by norm_num) ((f 1)⁻¹) (inv_pos.mpr hp₁)
    rw [one_mul] at h'
    rw [inv_mul_cancel₀ hp₁.ne.symm] at h'
    have h'' :=  hq ((f 1)⁻¹) (inv_pos.mpr hp₁) 1 (by norm_num)
    rw [one_mul] at h''
    rw [inv_mul_cancel₀ hp₁.ne.symm] at h''
    rw [← h''] at h'
    have := hq 1 (by norm_num) 1 (by norm_num)
    field_simp at this
    rw [this] at h'
    exact h'
  
  -- show that 1 is the unique fixed point
  -- starting with every a > 1 is not a fixed point
  have u : ∀ a > 1, f a ≠ a := by
    intro a pa ha
    have hi (n:ℕ): f (a^n) = a^n := by
      induction n
      · simp
        exact h₁
      case succ n hn =>
        calc f (a ^ (n + 1)) = f (a^n * a) := rfl
          _ = f ( a^n * f a) := by rw [ha]
          _ = a * f (a^n) := by apply hq; apply pow_pos; repeat linarith
          _ = a * a^n := by rw [hn]
          _ = a^(n+1) := by rw [mul_comm]; exact rfl
    rcases hl 1 (by norm_num) with ⟨t,ht⟩
    rcases pow_unbounded_of_one_lt t pa with ⟨n,_⟩
    have : f (a^n) < 1 := by
      apply ht
      linarith
    absurd this
    push_neg
    rw [hi n]
    convert pow_le_pow_left _ pa.lt.le n
    repeat simp
  
  -- then every a < 1 is not a fixed point
  have v : ∀ a, 0 < a ∧ a < 1 →  f a ≠ a := by
    intro a ⟨pa,pa₁⟩ ha
    have : a * f a⁻¹ = 1 := 
      calc a * f a⁻¹ = f (a⁻¹ * f a) := by apply Eq.symm; apply hq; rw [gt_iff_lt,inv_pos]; repeat linarith
        _ = f (a⁻¹ * a) := by rw [ha]
        _ = f 1 := by rw [inv_mul_cancel₀]; linarith
        _ = 1 := by rw [h₁]
    apply u a⁻¹
    rw [gt_iff_lt]
    apply one_lt_inv
    repeat assumption
    exact Eq.symm (DivisionMonoid.inv_eq_of_mul a (f a⁻¹) this)

  -- finishing the proof that 1 is the only fixed point
  have : ∀ a > 0, f a = a → a = 1 := by
    intro a pa ha
    rcases lt_trichotomy a 1 with _|_|_
    · absurd ha
      apply v
      constructor
      repeat assumption
    · assumption
    · absurd ha
      apply u
      assumption
  
  -- observe that x * f(x) is a fixed point by using y = x at the assumption
  intro x px
  apply Eq.symm
  apply DivisionMonoid.inv_eq_of_mul
  apply this
  · apply mul_pos
    exact px
    exact hp x px
  · apply hq
    repeat exact px