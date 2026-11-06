import Mathlib

/- Find all $f: \mathbb{Z} \rightarrow \mathbb{Z}$ such that  $$ x f(2 f(y)-x)+y^{2} f(2 x-f(y))=\frac{f(x)^{2}}{x}+f(y f(y)) $$  for all $x, y \in \mathbb{Z}$ such that $x \neq 0$. -/
theorem algebra_604659 :
    {f : ℤ → ℤ | ∀ x y, x ≠ 0 → x * f (2 * f y - x) + y ^ 2 * f (2 * x - f y) = (f x ^ 2 / x : ℚ) + f (y * f y)} = {fun x => 0, fun x => x ^ 2} := by
  -- Break the goal into two parts.
  ext f
  simp
  constructor
  . -- Prove the forward direction: the functional equation implies the two solutions.
    intro h₀
    -- Substitute y = 0 into h₀.
    have h₁ (x : ℤ) (hx : x ≠ 0) := h₀ x 0 hx
    -- Show that f(0) = 0.
    have h₂ : f 0 = 0 := by
      -- It suffices to show that p ∣ f(0) for all prime p.
      suffices ∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ f 0 by
        -- Assume on the contrary that f(0) ≠ 0.
        by_contra! h
        replace h : 0 < (f 0).natAbs := by
          simp [h]
        -- Since there are infinitely many primes, we can take a large prime p > |f(0)|.
        obtain ⟨p, hp', hp⟩ := Nat.exists_infinite_primes ((f 0).natAbs + 1)
        -- However, p ∣ f(0), so p ≤ |f(0)|, contradicting the assumption.
        replace this := Nat.le_of_dvd h (Int.natAbs_dvd_natAbs.mpr (this p hp))
        omega
      -- Now fix some prime p, and we shall show that p ∣ f(0).
      intro p hp
      -- Substitute x = p into h₁.
      have h₂ := h₁ p (by simp; apply (Nat.Prime.pos hp).ne')
      -- Since the expression is integer, p must divide f(p)², and hence f(p).
      replace h₂ : p * (p * f (2 * f 0 - p) - f 0) = (f p) ^ 2 := by
        field_simp [(Nat.Prime.pos hp).ne'] at h₂
        norm_cast at h₂ ⊢
        linarith
      have h₃ : (p : ℤ) ∣ f p := by
        apply @Prime.dvd_of_dvd_pow _ _ _ (Nat.prime_iff_prime_int.mp hp) _ 2
        rw [<-h₂]
        apply dvd_mul_right
      -- Now let f(p) = kp.
      obtain ⟨k, h₃⟩ := dvd_iff_exists_eq_mul_left.mp h₃
      -- Substitute f(p) = kp into the expression, simplify and get p ∣ f(0). 
      rw [h₃, mul_comm k, mul_pow, pow_two, mul_assoc] at h₂
      simp [(Nat.Prime.pos hp).ne'] at h₂
      replace h₂ : f 0 = p * (f (2 * f 0 - p) - k ^ 2) := by
        linarith
      rw [h₂]
      apply dvd_mul_right
    -- Substitute f(0) = 0 into h₁.
    simp [h₂] at h₁
    -- Show that f(x) = 0 or x² for each individual x.
    have h₃ (x : ℤ) : f x = 0 ∨ f x = x ^ 2 := by
      by_cases hx : x = 0
      . -- If x = 0, it is clear.
        simp [hx, h₂]
      . -- If x ≠ 0, we use h₁ with x and -x.
        have h₁' := h₁ (-x) (by simp [hx])
        specialize h₁ x hx
        field_simp [show -(x : ℚ) ≠ 0 by simp [hx]] at h₁ h₁'
        norm_cast at h₁ h₁'
        by_cases h₃ : f x = f (-x)
        . -- Suppose f(x) = f(-x), then f(x) = 0 or x².
          simp [<-h₃] at h₁
          replace h₁ : f x * (f x - x ^ 2) = 0 := by
            linarith
          simp at h₁
          rcases h₁ with (h₁ | h₁)
          . simp [h₁]
          . apply eq_of_sub_eq_zero at h₁
            simp [h₁]
        . -- Otherwise, subtract the two equations.
          have h₄ : (f x - f (-x)) * (f x + f (-x) + x ^ 2) = 0 := by
            linarith
          simp [show f x - f (-x) ≠ 0 by by_contra!; omega] at h₄
          -- Multiply the equation f(x) + f(-x) + x² = 0 by x² and then remove the term with f(-x) by h₁.
          replace h₄ := congr_arg (· * x ^ 2) h₄
          simp only [add_mul, show f (-x) * x ^ 2 = f x ^ 2 by rw [<-h₁]; ring] at h₄
          -- Now we have (2f(x) + x²)² + 3x⁴ = 0, and hence x = 0.
          have h₅ : x ^ 4 = 0 := by
            linarith [show x ^ 4 ≥ 0 by positivity, sq_nonneg (2 * f x + x ^ 2)]
          -- Now we have f(x) = 0 (or we may also derive a contradiction from the assumption x ≠ 0).
          left
          simp_all
    by_cases h₄ : ∀ x, f x = x ^ 2
    . -- If f(x) = x² for all x, we are done.
      right
      ext x
      simp [h₄]
    . -- Otherwise, there exists some integer t ≠ 0 such that f(t) = 0.
      push_neg at h₄
      obtain ⟨t, ht⟩ := h₄
      -- Note that t ≠ 0 because f(t) ≠ t² and f(0) = 0.
      have ht' : t ≠ 0 := by
        by_contra! h
        simp_all
      replace ht : f t = 0 := by
        specialize h₃ t
        simp [ht] at h₃
        exact h₃
      -- Substitute y = t into the original equation.
      have h₅ (x : ℤ) (hx : x ≠ 0) : t = 0 ∨ f (2 * x) = 0 := by
        specialize h₀ x t hx
        specialize h₁ x hx
        simp [ht, h₂, h₁] at h₀
        exact h₀
      -- Therefore, we have f(2x) = 0 for all x.
      replace h₅ (x : ℤ) : f (2 * x) = 0 := by
        by_cases hx : x = 0
        . -- If x = 0, we are done.
          simp [hx, h₂]
        . -- Otherwise, we have f(2x) = 0.
          specialize h₅ x hx
          simp [ht'] at h₅
          exact h₅
      -- Replace x by 2x in the original equation to get y²f(4x - f(y)) = f(yf(y)) for all x ≠ 0.
      have h₆ (x y : ℤ) (hx : x ≠ 0) : y ^ 2 * f (4 * x - f y) = f (y * f y) := by
        specialize h₀ (2 * x) y (by simp [hx])
        have h₅' := h₅ x
        specialize h₅ (f y - x)
        rw [mul_sub] at h₅
        simp [h₅', h₅, <-mul_assoc] at h₀
        norm_cast at h₀
      -- Show that f(x) ≠ x² for all odd x.
      have h₇ (x : ℤ) (hx : x ≠ 0) (hx' : Odd x) : f x ≠ x ^ 2 := by
        -- Assume there is such odd x such that f(x) ≠ x².
        by_contra! h₇
        replace h₆ (k : ℤ) (hk : k ≠ 0) := h₆ k x hk
        simp [h₇, show x * x ^ 2 = x ^ 3 by ring] at h₆
        by_cases h₈ : f (x ^ 3) = 0
        . -- Suppose f(x³) = 0.
          -- This means that f(4k - x²) = 0 for any k ∈ ℤ.
          simp [h₈, hx] at h₆
          -- Also note that f(x² - 4k) = 0 for any k ∈ ℤ.
          have h₆' (k : ℤ) (hk : k ≠ 0) : f (x ^ 2 - 4 * k) = 0 := by
            specialize h₆ k hk
            have h' : x ^ 2 - 4 * k ≠ 0 := by
              by_contra!
              replace this : 2 ^ 2 ∣ x ^ 2 := by
                simp [show x ^ 2 = 4 * k by linarith]
              rw [Int.pow_dvd_pow_iff (by norm_num)] at this
              absurd hx'
              simp [even_iff_two_dvd, this]
            specialize h₁ (x ^ 2 - 4 * k) h'
            symm at h₁
            qify at h'
            field_simp [h₆] at h₁
            exact h₁
          -- Show that for any p ≠ ±x², f(p) = 0.
          have h₉ (p : ℤ) (hp : p ≠ -x ^ 2) (hp' : p ≠ x ^ 2) : f p = 0 := by
            by_cases hp'' : Even p
            . -- Suppose p is even.
              -- Then p = 2q for some k ∈ ℤ.
              obtain ⟨q, rfl⟩ := even_iff_two_dvd.mp hp''
              exact h₅ q
            . -- Suppose p is odd.
              -- Find k ≠ 0 such that 4k = x² + p or 4k = x² - p.
              have h₉ : (x ^ 2 + p) % 4 = 0 ∨ (x ^ 2 + p) % 4 = 2 := by
                have h₉ : Even (x ^ 2 + p) := by
                  simp at hp''
                  apply Odd.add_odd (Odd.pow hx') hp''
                rw [even_iff_two_dvd] at h₉
                omega
              rcases h₉ with (h₉ | h₉)
              . -- Suppose (x ^ 2 + p) % 4 = 0, then 4k = x² + p.
                rw [<-Int.dvd_iff_emod_eq_zero, dvd_iff_exists_eq_mul_right] at h₉
                obtain ⟨k, h₉⟩ := h₉
                -- Note that k ≠ 0 because p ≠ ±x², so we can use h₆.
                specialize h₆ k (by omega)
                simp [<-h₉] at h₆
                exact h₆
              . -- Suppose (x ^ 2 + p) % 4 = 2, then 4k = x² - p.
                replace h₉ : (x ^ 2 - p) % 4 = 0 := by
                  simp [Odd] at hp''
                  obtain ⟨p', hp''⟩ := hp''
                  omega
                rw [<-Int.dvd_iff_emod_eq_zero, dvd_iff_exists_eq_mul_right] at h₉
                obtain ⟨k, h₉⟩ := h₉
                -- Note that k ≠ 0 because p ≠ ±x², so we can use h₆'.
                specialize h₆' k (by omega)
                simp [<-h₉] at h₆'
                exact h₆'
          -- Show that x = ±1.
          have h₁₀ : x = 1 ∨ x = -1 := by
            -- Assume on the contrary that x ≠ ±1, then we derive a contradiction.
            by_contra! h₁₀
            have h₉a : x ≠ -x ^ 2 := by
              by_contra!
              replace this : x * (x + 1) = 0 := by
                linarith
              simp [hx] at this
              absurd h₁₀.2
              linarith
            have h₉b : x ≠ x ^ 2 := by
              by_contra!
              replace this : x * (x - 1) = 0 := by
                linarith
              simp [hx] at this
              absurd h₁₀.1
              linarith
            specialize h₉ x h₉a h₉b
            symm at h₇
            simp [hx, h₉] at h₇
          rcases h₁₀ with (h₁₀ | h₁₀)
          -- Replace (x, y) by (5, x) in the original equation to derive a contradiction.
          all_goals
            specialize h₀ 5 x (by norm_num)
            simp [h₁₀] at h₇ h₉ h₀
            simp [h₇, h₉ (-3) (by norm_num) (by norm_num), h₉ 9 (by norm_num) (by norm_num), h₉ 5 (by norm_num) (by norm_num)] at h₀
        . -- Suppose f(x³) = x³.
          have h₃' := h₃ (x ^ 3)
          simp [h₈] at h₃'
          simp [h₃'] at h₆
          -- This means that f(4k - x²) = x⁴ for any k ∈ ℤ, which is nonsense (just take k = x² suffices).
          specialize h₆ (x ^ 2) (by simp [hx])
          ring_nf at h₆
          have h₃'' := h₃ (x ^ 2 * 3)
          rcases h₃'' with (h₃'' | h₃'')
          . symm at h₆
            simp [h₃'', hx] at h₆
          . simp [h₃''] at h₆
            ring_nf at h₆
            have : x ^ 6 ≠ 0 := by by_contra!; simp [hx] at this
            omega
      -- Now conclude that f(x) = 0 for all x.
      left
      ext x
      by_cases hx : Odd x
      . -- For odd x, we have proved that f(x) ≠ x².
        specialize h₇ x (by by_contra!; norm_num [this] at hx) hx
        specialize h₃ x
        simp [h₇] at h₃
        exact h₃
      . -- For even x, let x = 2k and f(2k) = 0.
        simp [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at hx
        obtain ⟨k, rfl⟩ := hx
        specialize h₅ k
        exact h₅
  . -- Prove the backward direction: the two solutions do satisfy the functional equation.
    rintro (rfl | rfl)
    all_goals
      intro x y hx
      field_simp
      try ring

