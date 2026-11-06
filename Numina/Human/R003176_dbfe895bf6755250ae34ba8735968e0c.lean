import Mathlib
/- Example 17 (1991 Japan Mathematical Olympiad Preliminary Problem) How many pairs of positive integer solutions $(x, y)$ satisfy $\frac{1}{x+1}+\frac{1}{y}+\frac{1}{(x+1) y}=\frac{1}{1991}$? -/
theorem algebra_159347 (A : Finset (ℕ × ℕ)) (hA : (↑A : Set (ℕ × ℕ)) = {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ((1 : ℚ) / (x + 1) + 1 / y + 1 / ((x + 1) * y) = 1 / 1991)}) : A.card = 64:= by
  -- Define B as the set of divisors of 1991 * 1992
  set B:= Nat.divisors (1991 * 1992) with hB
  clear_value B
  -- Define function f that maps divisors to solution pairs
  set f : ℕ → (ℕ × ℕ):= fun n => (1990 + n, (1991 * 1992) / n + 1991) with hf
  clear_value f
  -- Prove that f is a bijection from B to A
  have h1 : Set.BijOn f (↑B : Set ℕ) (↑A : Set (ℕ × ℕ)):= by
    constructor
    .
      -- Prove that f maps B into A (MapsTo)
      simp [Set.MapsTo]
      intro n h
      suffices f n ∈ (↑A : Set (ℕ × ℕ)) by exact this
      subst B
      replace h : n ∣ 1991 * 1992:= by exact Nat.dvd_of_mem_divisors h
      simp [hf]
      simp at h
      rcases h with ⟨k, h⟩
      have g : n ≠ 0:= by
        by_contra H
        subst n
        simp at h
      rw [show 3966072 / n = k by exact Eq.symm (Nat.eq_div_of_mul_eq_right g (id (Eq.symm h)))]
      suffices (1990 + n, k + 1991) ∈ (↑A : Set (ℕ × ℕ)) by exact this
      rw [hA]
      simp
      replace h : k = (3966072 : ℚ) / n:= by
        qify at h
        field_simp
        rw [h]
        ring
      rw [h]
      field_simp
      ring_nf
    .
      -- Prove that f is injective and surjective
      refine ⟨?_, ?_⟩
      .
        -- Prove injectivity: if f(n) = f(m) then n = m
        simp [Set.InjOn]
        intro n _ m _ hnm
        simp [hf] at hnm
        exact hnm.1
      .
        -- Prove surjectivity: every element in A is in the image of f
        simp [Set.SurjOn]
        intro ⟨x, y⟩ h
        simp
        rw [hA] at h
        simp at h
        rcases h with ⟨hx, hy, h⟩
        -- Transform the equation to isolate variables
        replace h : (((↑x : ℚ) + 1)⁻¹ + (↑y)⁻¹ + (↑y)⁻¹ * ((↑x : ℚ) + 1)⁻¹) * ((x + 1) * y) = 1991⁻¹ * ((x + 1) * y):= by rw [h]
        rw [show (((↑x : ℚ) + 1)⁻¹ + (↑y)⁻¹ + (↑y)⁻¹ * ((↑x : ℚ) + 1)⁻¹) * ((x + 1) * y) = 1 + x + 1 + y by field_simp ; ring_nf] at h
        field_simp at h
        -- Convert to integer equation: (x-1990)(y-1991) = 1991*1992
        replace h : ((x : ℤ) - 1990) * (y - 1991) = 1991 * 1992:= by
          qify
          linarith
        -- Prove x ≥ 1990 by contradiction
        have g1 : x ≥ 1990:= by
          zify
          by_contra H
          simp at H
          have g2 : y < 1991:= by
            zify
            by_contra H1
            simp at H1
            replace H1 : (↑y : ℤ) - 1991 ≥ 0:= by
              zify at H1
              linarith
            replace H : (↑x : ℤ) - 1990 ≤ 0:= by
              zify at H
              linarith
            have H2 : (1991 : ℤ) * 1992 ≤ 0:= by
              rw [←h]
              exact Int.mul_nonpos_of_nonpos_of_nonneg H H1
            linarith
          replace h : (1990 - x) * (1991 - y) = 1991 * 1992:= by
            zify
            replace H : 1990 ≥ x:= by omega
            replace g2 : 1991 ≥ y:= by omega
            field_simp
            linarith
          replace H : 1990 - x ≤ 1989:= by omega
          replace g2 : 1991 - y ≤ 1990:= by omega
          replace H : (1990 - x) * (1991 - y) ≤ 1989 * 1990:= by exact Nat.mul_le_mul H g2
          linarith
        -- Prove y ≥ 1991 by contradiction
        have g2 : y ≥ 1991:= by
          by_contra H
          simp at H
          zify at g1 H
          replace g1 : (↑x : ℤ) - 1990 ≥ 0:= by omega
          replace H : (↑y : ℤ) - 1991 ≤ 0:= by omega
          replace h : (1991 : ℤ) * 1992 ≤ 0:= by
            rw [←h]
            exact Int.mul_nonpos_of_nonneg_of_nonpos g1 H
          linarith
        -- Convert back to natural numbers
        replace h : (x - 1990) * (y - 1991) = 1991 * 1992:= by
          zify
          field_simp
          linarith
        -- Prove that x-1990 is a divisor of 1991*1992
        have g3 : x - 1990 ∈ B:= by
          subst B
          simp
          use y - 1991
          linarith
        -- Calculate y in terms of x-1990
        replace h : y - 1991 = (1991 * 1992) / (x - 1990):= by
          have g : x - 1990 ≠ 0:= by
            by_contra H
            rw [H] at h
            simp at h
          rw [←h]
          rw [show (x - 1990) * (y - 1991) = (y - 1991) * (x - 1990) by linarith]
          field_simp
        replace h : y = (1991 * 1992) / (x - 1990) + 1991:= by omega
        -- Show that (x,y) is in the image of f
        use x - 1990
        refine ⟨g3, ?_⟩
        rw [h]
        simp [hf]
        omega
  -- Use the bijection to prove that |A| = |B|
  have h2 : B.card = A.card:= by
    replace h1:= Set.BijOn.equiv f h1
    simp at h1
    apply Nat.card_congr at h1
    simp at h1
    exact h1
  -- Rewrite the goal using the cardinality equality
  rw [←h2]
  subst B
  -- Use native decision procedure to compute the number of divisors
  native_decide
