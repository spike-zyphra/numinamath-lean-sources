import Mathlib

/- 10. (GRE 3) Let $g: \mathbb{C} \rightarrow \mathbb{C}, w \in \mathbb{C}, a \in \mathbb{C}, w^{3}=1(w \neq 1)$. Show that there is one and only one function $f: \mathbb{C} \rightarrow \mathbb{C}$ such that  $$ f(z)+f(w z+a)=g(z), \quad z \in \mathbb{C} $$  Find the function $f$. -/
theorem algebra_24188 {g : ℂ → ℂ} {w a : ℂ} (hw : w ^ 3 = 1 ∧ w ≠ 1) :
    ∃! f : ℂ → ℂ, ∀ z, f z + f (w * z + a) = g z := by 
  simp only [ExistsUnique]
  have : ∀ f : ℂ → ℂ, (∀ z, f z + f (w * z + a) = g z) ↔ f = (fun z => (g z + g (w ^ 2 * z + w * a + a) - g (w * z + a)) / 2) := by
    intro f
    have hw' : w ≠ 0 := by
      intro h
      simp [h] at hw
    -- use properties of roots of unity
    have hw'' : w ^ 2 + w + 1 = 0 := by 
      have : (w - 1) * (w ^ 2 + w + 1) = 0 := by
        ring
        rw [hw.1] 
        simp
      have : w - 1 = 0 ∨ w ^ 2 + w + 1 = 0 := mul_eq_zero.mp this
      have : ¬ (w - 1 = 0) := by 
        intro h
        have := hw.2
        rw [sub_eq_zero] at h
        tauto
      tauto
    -- 10. Plugging in $w z+a$ instead of $z$ into the functional equation, we obtain $$ f(w z+a)+f\left(w^{2} z+w a+a\right)=g(w z+a) .
    have : (∀ z, f z + f (w * z + a) = g z) ↔ (∀ z, f (w * z + a) + f (w ^ 2 * z + w * a + a) = g (w * z + a)) := by
      apply Iff.intro
      · intro H
        intro z
        specialize H (w * z + a)
        rw [← H]
        ring_nf
      · intro H
        intro z
        specialize H ((z - a) / w)
        have : w * ((z - a) / w) + a = z := by 
          field_simp
        rw [this] at H
        have : w ^ 2 * ((z - a) / w) + w * a + a = w * z + a := by
          field_simp
          ring
        rw [this] at H
        exact H
    -- $$ By repeating this process, this time in (1), we get $$ f\left(w^{2} z+w a+a\right)+f(z)=g\left(w^{2} z+w a+a\right) $$ 
    have : (∀ z, f z + f (w * z + a) = g z) ↔ ∀ z, f (w ^ 2 * z + w * a + a) + f z = g (w ^ 2 * z + w * a + a) := by
      apply Iff.intro
      · intro H
        intro z
        specialize H (w ^ 2 * z + w * a +  a)
        have : w * (w ^ 2 * z + w * a + a) + a = a * (w ^ 2 + w + 1) + z := by 
          ring_nf
          rw [hw.1]
          ring
        rw [this] at H
        rw [← H, hw'']
        ring_nf
      · intro H
        · intro z
          specialize H ((z - (w * a + a)) / w ^ 2)
          have : w ^ 2 * ((z - (w * a + a)) / w ^ 2) + w * a + a = z := by
            field_simp
            ring
          rw [this] at H
          have : (z - (w * a + a)) / w ^ 2 = w * z + a := by 
            field_simp
            ring
            rw [hw.1]
            linear_combination (norm := ring) -a * hw''
          rw [this] at H
          exact H
    -- Solving the system of linear equations (1), (2) and the original functional equation, we easily get $$ f(z)=\frac{g(z)+g\left(w^{2} z+w a+a\right)-g(w z+a)}{2} . $$ 
    apply Iff.intro
    · intro H₁
      have H₂ : (∀ z, f (w * z + a) + f (w ^ 2 * z + w * a + a) = g (w * z + a)) := by tauto
      have H₃ :  (∀ z, f (w ^ 2 * z + w * a + a) + f z = g (w ^ 2 * z + w * a + a)) := by tauto
      ext z
      specialize H₁ z
      specialize H₂ z
      specialize H₃ z
      linear_combination (norm := ring) ((H₁) + (-H₂ + H₃)) / 2
    · intro H
      simp [H]
      intro z
      have : w ^ 2 * (w * z + a) + w * a + a = z := by
        linear_combination (norm := ring)  hw.1 * z + a * hw''
      rw [this]
      ring
  -- This function thus uniquely satisfies the original functional equation.
  use fun z => (g z + g (w ^ 2 * z + w * a + a) - g (w * z + a)) / 2
  simp [this]