import Mathlib

/- Trouver toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles qu'il existe un réel $A$ vérifiant $A>f(x)$ pour tout $x \in \mathbb{R}$, et telles que pour tous réels $x, y$, on ait :

$$
f(x f(y))+y f(x)=x f(y)+f(x y)
$$ -/
theorem algebra_607732 :
    {f : ℝ → ℝ | (∃ A : ℝ, ∀ x, A > f x) ∧ (∀ x y, f (x * f y) + y * f x = x * f y + f (x * y))} = {fun x => 0, fun x => if x < 0 then 2 * x else 0} := by
  ext f
  apply Iff.intro
  . -- Solve the condition to get the two solutions.
    intro h
    simp at h ⊢
    obtain ⟨⟨A, hA⟩, h⟩ := h
    -- Show that f(0) = 0.
    have h₀ : f 0 = 0 := by
      -- Specialize the functional equation to (x, y) = (0, 1).
      have := h 0 1
      simp at this
      linarith only [this]
    -- Show that f(1) = 0.
    have h₁ : f 1 = 0 := by
      by_contra!
      -- Use x = A / f(1) and y = 1 in the functional equation.
      specialize h (A / f 1) 1
      simp [this] at h
      -- f(A) = A contradicts with the fact that f(x) < A for all x.
      linarith only [hA A, h]
    -- Set x = 1 in the functional equation.
    have h₂ := h 1
    simp [h₁, <-mul_two] at h₂
    -- Show that f(x) ≤ 0 for all x.
    have h₃ : ∀ x, f x ≤ 0 := by
      by_contra!
      -- Assume on the contrary that f(z) > 0 for some z.
      obtain ⟨z, hz⟩ := this
      -- Iterate the functional equation f(f(y)) = 2f(y) to get a contradiction.
      have (n : ℕ) : ∃ z', f z' = 2 ^ n * f z := by
        induction n with
        | zero =>
          simp [hz]
        | succ n hn =>
          obtain ⟨z', hz'⟩ := hn
          use f z'
          rw [h₂, hz', pow_add]
          ring
      -- We would have A > 0.
      have hA' : A > 0 := by
        linarith only [hz, hA z]
      -- Let n be an integer such that 2ⁿf(z) ≥ A.
      let n := ⌈Real.logb 2 (A / f z)⌉
      have h' : (2 : ℝ) ^ (n : ℝ) ≥ 2 ^ (Real.logb 2 (A / f z)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        simp [n]
        apply Int.le_ceil
      -- Let m be a natural number such that 2ⁿf(z) ≥ A.
      let m := n.natAbs
      replace h' : (2 : ℝ) ^ m ≥ A / f z := by
        calc
          (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℤ) := by simp
          _ ≥ (2 : ℝ) ^ (n : ℤ) := by
            rw [ge_iff_le, zpow_le_zpow_iff_right₀ (by norm_num)]
            simp only [m]
            apply Int.le_natAbs
          _ = (2 : ℝ) ^ (n : ℝ) := by simp
          _ ≥ 2 ^ (Real.logb 2 (A / f z)) := h'
          _ = A / f z := by
            rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      specialize this m
      obtain ⟨z', hz'⟩ := this
      -- Now we find z' such that f(z') ≥ A, contradiction.
      have : f z' ≥ A := by
        calc
          f z' = 2 ^ m * f z := by rw [hz']
          _ ≥ (A / f z) * f z := by
            rw [ge_iff_le, mul_le_mul_right (by positivity)]
            exact h'
          _ = A := by
            rw [div_mul_cancel₀ _ hz.ne']
      absurd this
      simp [hA z']
    -- We suppose f(x) ≠ 0 for some x ≠ 0 and prove that the function must be equal to the other solution.
    rw [or_iff_not_imp_left]
    intro h₄
    -- Show that f(x) < 0 for all x < 0.
    have h₅ (y : ℝ) : y < 0 → f y < 0 := by
      intro hy
      -- Suppose f(y) ≥ 0 for some y, then y ≥ 0.
      contrapose! hy
      replace hy : f y = 0 := by
        linarith only [hy, h₃ y]
      -- Substitute f(y) = 0 into the functional equation.
      replace h (x : ℝ) := h x y
      simp [hy, h₀] at h
      by_cases hy' : y = 0
      . simp [hy']
      . -- Let x be a number such that f(x) ≠ 0.
        have h₅ : ∃ x : ℝ, f x ≠ 0 := by
          contrapose! h₄
          ext x
          simp [h₄]
        obtain ⟨x, hx⟩ := h₅
        -- Since f(x) ≤ 0, f(x) < 0.
        replace hx := lt_of_le_of_ne (h₃ x) hx
        -- We cannot have y < 0, otherwise f(xy) > 0.
        by_contra! hy'
        specialize h x
        linarith only [show 0 < f (x * y) by nlinarith, h₃ (x * y)]
    -- Show that f(x) = 0 for all x ≥ 0.
    have h₆ (x : ℝ) : x > 0 → f x = 0 := by
      intro hx
      -- Substitute y = 1 / x into the functional equation.
      have h₆ := h x (1 / x)
      -- Swap x and (1 / x) to get another equation.
      have h₇ := h (1 / x) x
      simp [hx.ne', h₁] at h₆ h₇
      -- Combine two equations.
      have h₈ : f (1 / x * f x) + f (x * f (1 / x)) = 0 := by
        ring_nf
        linarith only [h₆, h₇]
      -- Since f ≤ 0, both terms must vanish.
      have h₉ : f (1 / x * f x) = 0 := by
        linarith only [h₈, h₃ (1 / x * f x), h₃ (x * f (1 / x))]
      -- Assume on the contrary that f(x) ≠ 0.
      by_contra! h₁₀
      replace h₁₀ := lt_of_le_of_ne (h₃ x) h₁₀
      -- f(x) < 0 implies f(x) / x < 0, which cannot be true due to the result just proved.
      have h₁₁ : 1 / x * f x < 0 := by
        rw [div_mul_comm, mul_one, div_lt_iff₀]
        simp [h₁₀]
        exact hx
      specialize h₅ (1 / x * f x) h₁₁
      linarith only [h₉, h₅]
    -- Show that f(-y) = yf(-1) for y > 0.
    have h₇ (y : ℝ) : y > 0 → f (-y) = y * f (-1) := by
      intro hy
      -- Substitute x = -1 into the functional equation.
      specialize h (-1) y
      simp [h₆ y hy, h₀] at h
      exact h.symm
    -- Show that f(-1) = -2.
    have h₈ : f (-1) = -2 := by
      -- Substitute x = -1 into the f(f(y)) = 2f(y) equation.
      specialize h₂ (-1)
      rw [<-neg_neg (f (-1)), h₇ (-f (-1)) (by linarith only [h₅ (-1) (by norm_num)])] at h₂
      replace h₂ : f (-1) * (f (-1) + 2) = 0 := by
        linarith only [h₂]
      simp [(h₅ (-1) (by norm_num)).ne'.symm] at h₂
      linarith only [h₂]
    -- Now show that f(x) = 0 for x < 0 and f(x) = 2x for x ≥ 0.
    ext x
    split_ifs with hx
    . -- If x < 0, apply h₇ and h₈.
      rw [<-neg_neg x, h₇ (-x) (by linarith), h₈]
      ring
    . by_cases hx' : x = 0
      . simp [hx', h₀]
      . -- If x > 0, apply h₆.
        apply h₆
        contrapose hx'
        simp at hx hx' ⊢
        linarith only [hx, hx']
  . -- Prove that the two functions indeed satisfy the condition.
    intro h
    simp at h ⊢
    obtain h | h := h
    . -- Show that f(x) = 0 satisfies the condition.
      refine ⟨?_, ?_⟩
      . use 1
        simp [h]
      . simp [h]
    . -- Show that f(x) = (if x < 0 then 2x else 0) satisfies the condition.
      refine ⟨?_, ?_⟩
      . use 1
        intro x
        simp [h]
        split_ifs with h
        all_goals
          linarith
      . intro x y
        by_cases hx : x < 0
        . by_cases hy : y < 0
          . -- Case 1: x, y < 0.
            have hxy : ¬x * y < 0 := by
              nlinarith
            have hxy' : ¬x * (2 * y) < 0 := by
              linarith
            have hfy : f y < 0 := by
              simp [h, hy]
              linarith
            simp [h, hx, hy, hxy, hxy', hfy]
            ring
          . -- Case 2: x < 0 but y ≥ 0.
            by_cases hy' : y = 0
            . simp [hy', h]
            . rw [<-ne_eq] at hy'
              replace hy : y > 0 := by
                apply lt_of_le_of_ne (by linarith) (hy'.symm)
              replace hy' : ¬y < 0 := by
                linarith
              have hxy : x * y < 0 := by
                nlinarith
              simp [h, hx, hy, hy', hxy]
              ring
        . by_cases hy : y < 0
          . -- Case 3: x ≥ 0 but y < 0.
            by_cases hx' : x = 0
            . simp [hx', h]
            . rw [<-ne_eq] at hx'
              replace hx : x > 0 := by
                apply lt_of_le_of_ne (by linarith) (hx'.symm)
              replace hx' : ¬x < 0 := by
                linarith
              have hxy : x * y < 0 := by
                nlinarith
              have hxy' : x * (2 * y) < 0 := by
                linarith
              simp [h, hx, hx', hy, hxy, hxy']
              ring
          . -- Case 4: x, y ≥ 0.
            have hxy : ¬x * y < 0 := by
              nlinarith
            simp [h, hx, hy, hxy]
