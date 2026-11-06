import Mathlib

theorem algebra_237101 (f : ℝ → ℝ) :
    (∀ x > 0, f x > 0) ∧ f 1 = 1 ∧
    (∀ a b, f (a + b) * (f a + f b) = 2 * f a * f b + a ^ 2 + b ^ 2) ↔
    ∀ x, f x = x := by
  constructor
  · -- First prove the converse, (i.e., from the three axioms to f(x) = x)
    rintro ⟨h1, h2, h⟩
    
    have h0 : f 0 = 0 := by
      have eq1 := h 1 0
      norm_num [h2] at eq1
      nlinarith

    have eq1 : ∀ x > 0, f x = x := by
      intro x hx
      have eq2 := h x 0
      simp [h0] at eq2
      have hx2 : f x ^ 2 = x ^ 2 := by 
        nlinarith 
      have hx5 : f x > 0 := h1 x hx
      have hx6 : x > 0 := by linarith
      have eq3 : f x = x := by
        nlinarith [sq_pos_of_pos hx5, sq_pos_of_pos hx6]
      exact_mod_cast eq3

    -- Now, extend to real numbers y < 0

    have eqn1 : ∀ y < 0, f y = y := by 
      intro y hy 
      have h4 : f (-y) = -y := by
        have h5 : -y > 0 := by linarith
        specialize eq1 (-y) h5
        linarith
      have eq4 : f y * f (-y) = -y^ 2 := by
        have h3 := h y (-y)
        have h5 : y + -y = (0 : ℝ) := by ring
        simp [h5, h0] at h3
        linarith
      have eqy : f y = y := by
        rw [h4] at eq4
        have h5 : y ≠ 0 := by linarith
        have eq6 : f y * (-y) = -y ^ 2 := by linarith
        have eq7 : f y = y := by
          apply (mul_right_inj' (show -y ≠ 0 by
            intro h6
            have : y = 0 := by linarith
            contradiction
          )).mp 
          linarith
        exact_mod_cast eq7
      exact_mod_cast eqy

    intro x 
    by_cases hpos : x > 0
    · -- Case x > 0
      specialize eq1 x hpos
      linarith
    by_cases hneg : x < 0
    · -- Case x < 0
      specialize eqn1 x hneg
      linarith
    · -- Case x = 0
      have h4 : x = 0 := by linarith 
      rw [h4]
      linarith [h0]

  · -- First the more direction
    intro h
    constructor
    · -- Show that for x>0, f(x) >0
      intro x hx
      have hx2 : f x = x := h x
      rw [hx2]
      nlinarith
    constructor
    · -- Show f 1 = 1
      specialize h 1
      norm_num at h ⊢  -- Apply h
      all_goals linarith
    · -- Show f(a+b)(f(a)+f(b)) = 2f(a)f(b) + a^2 + b^2
      intro a b
      have ha : f a = a := h a
      have hb : f b = b := h b
      have hab : f (a + b) = a + b := by
        apply h
      rw [ha, hb, hab]
      all_goals nlinarith