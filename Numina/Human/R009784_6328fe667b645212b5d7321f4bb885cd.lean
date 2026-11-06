import Mathlib

/- Find all real $a$ for which there exists a function $f: \mathbb{R} \rightarrow \mathbb{R}$ such that $f(x-f(y))=f(x)+a[y]$ for every real $x$ и $y$ ( $[y]$ denotes the integral part of $y$ ).

Answer: $a=-n^{2}$ for arbitrary integer $n$. -/
theorem algebra_604369 :
    {a : ℝ | ∃ f : ℝ → ℝ, ∀ x y, f (x - f y) = f x + a * ⌊y⌋} = {a : ℝ | ∃ n : ℤ, a = -n ^ 2} := by
  -- First simplify the goal into two parts.
  ext a
  apply Iff.intro
  . -- Show that the condition implies that a = -n² for some n ∈ ℤ.
    rintro ⟨f, h₀⟩
    simp
    by_cases ha : a = 0
    . -- If a = 0, this is trivial.
      use 0
      simp [ha]
    . -- Now assume that a ≠ 0.
      -- Prove a lemma: f(y) = f(z) implies ⌊y⌋ = ⌊z⌋.
      have h₁ : ∀ y z, f y = f z → ⌊y⌋ = ⌊z⌋ := by
        intro y z
        intro h₁
        -- Substitute x = 0 and y = y or z respectively in the original equation.
        have g₀ := h₀ 0 y
        have g₁ := h₀ 0 z
        rw [<-h₁] at g₁
        rw [<-ne_eq] at ha
        rify
        rw [<-mul_left_inj' ha]
        linarith
      -- Prove a stronger result: f(y) = f(z) ↔ ⌊y⌋ = ⌊z⌋.
      replace h₁ : ∀ y z, f y = f z ↔ ⌊y⌋ = ⌊z⌋ := by
        intro y z
        apply Iff.intro <;> intro h₂
        . exact h₁ y z h₂
        . -- Show that ⌊y⌋ = ⌊z⌋ implies f(y) = f(z).
          -- Substitute y = y or z respectively in the original equation.
          have (x : ℝ) : ⌊x - f y⌋ = ⌊x - f z⌋ := by
            have g₀ := h₀ x y
            have g₁ := h₀ x z
            rw [<-h₂] at g₁
            have g₂ := g₀ ▸ g₁.symm
            -- Apply the previous result.
            apply h₁ _ _ g₂
          -- Substitute x = (f y + f z) / 2.
          specialize this ((f y + f z) / 2)
          -- Now ⌊-(f y - f z) / 2⌋ = ⌊(f y - f z) / 2⌋.
          -- Let n = ⌊-(f y - f z) / 2⌋ = ⌊(f y - f z) / 2⌋.
          let n := ⌊(f y - f z) / 2⌋
          have hn : ⌊(f y - f z) / 2⌋ = n := by
            rfl
          have hn' : ⌊-(f y - f z) / 2⌋ = n := by
            simp [n]
            ring_nf at this ⊢
            exact this
          rw [Int.floor_eq_iff] at hn hn'
          -- Now n ≤ (f y - f z) / 2 < n + 1 and -n - 1 < (f y - f z) / 2 ≤ -n, so n = 0.
          have : (n : ℝ) ≤ 0 ∧ (n : ℝ) > -1 := by
            exact ⟨by linarith only [show (n : ℝ) ≤ -n by linarith], by linarith only [show (-n - 1 : ℝ) < n + 1 by linarith]⟩
          norm_cast at this
          simp at this
          replace this : n = 0 := by
            omega
          -- Substitute n = 0 into previous hypotheses.
          rw [this] at hn hn'
          -- Now f(y) = f(z).
          linarith
      -- Now we claim that f(m) ∈ ℤ for any m ∈ ℤ.
      have h₂ : ∀ m : ℤ, ∃ n : ℤ, f m = n := by
        intro m
        -- Substitute y = m into the original equation.
        have h₂ (x : ℝ) := h₀ x m
        simp at h₂
        -- Assume on the contrary that f(m) ∉ ℤ.
        by_contra!
        -- Let s = f(m) - ⌊f(m)⌋.
        let s := f m - ⌊f m⌋
        -- Then 0 < s < 1.
        have hs : 0 < s ∧ s < 1 := by
          refine ⟨?_, ?_⟩
          . -- Show that s > 0.
            have h : 0 ≤ s := by
              simp [s]
            -- Assume on the contray that s = 0.
            by_contra! h'
            -- Then f(m) = ⌊f(m)⌋.
            specialize this ⌊f m⌋
            replace h : s = 0 := by
              linarith
            simp only [s] at h
            absurd this
            linarith only [h]
          . -- Show that s < 1.
            simp only [s]
            apply add_lt_of_lt_sub_right
            simp
            rw [add_comm]
            apply Int.lt_floor_add_one
        -- Let t = (1 - s) / 2.
        let t := (1 - s) / 2
        -- We have ⌊-f(m)⌋ = ⌊-t - f(m)⌋.
        have h₃ : ⌊-t - f m⌋ = ⌊-f m⌋ := by
          rw [<-neg_sub, Int.floor_neg, Int.floor_neg]
          simp
          rw [Int.ceil_eq_iff]
          nth_rw 2 [show f m = ⌊f m⌋ + s by simp [s]]
          nth_rw 3 [show f m = ⌊f m⌋ + s by simp [s]]
          -- Use 0 < t and s + t < 1 to prove the result. Tedious justification of details.
          refine ⟨?_, ?_⟩
          . calc
              ⌈f m⌉ - 1 < (f m + 1) - 1 := by
                rw [sub_lt_sub_iff_right]
                apply Int.ceil_lt_add_one
              _ = ⌊f m⌋ + s := by
                simp [s]
              _ < ⌊f m⌋ + s + t := by
                linarith [show 0 < t by simp [t]; linarith]
          . calc
              ⌊f m⌋ + s + t ≤ ⌊f m⌋ + 1 := by
                clear_value s
                linarith [show s + t < 1 by simp [t]; linarith]
              _ = ⌈f m⌉ := by
                symm
                norm_cast
                rw [Int.ceil_eq_iff]
                refine ⟨?_, ?_⟩
                . nth_rw 2 [show f m = ⌊f m⌋ + s by simp [s]]
                  simp [hs.1]
                . nth_rw 1 [show f m = ⌊f m⌋ + s by simp [s]]
                  simp
                  exact le_of_lt hs.2
              _ ≤ ⌈f m⌉ := by
                simp
        -- Substitute x = 0 and -t respectively in h₂.
        have h₄ := h₂ 0
        have h₅ := h₂ (-t)
        simp at h₄ h₅
        -- Since ⌊-f(m)⌋ = ⌊-t - f(m)⌋, we have f(-f(m)) = f(-t - f(m)).
        replace h₃ := (h₁ (-t - f m) (-f m)).mpr h₃
        -- Combine h₃, h₄ and h₅.
        replace h₃ := h₄.symm ▸ h₃.symm ▸ h₅
        clear h₄ h₅
        -- Now f(0) = f(-t)
        replace h₃ : f 0 = f (-t) := by
          linarith only [h₃]
        -- Now apply h₁ again to get ⌊0⌋ = ⌊-t⌋.
        simp [h₁] at h₃
        -- Contradiction with 0 = ⌊-t⌋ = -1.
        symm at h₃
        rw [Int.floor_eq_iff] at h₃
        simp at h₃
        linarith only [h₃.1, show 0 < t by simp [t]; linarith]
      -- Setting y = 1 in h₀.
      have h₃ (x : ℤ) := h₀ x 1
      simp at h₃
      -- Show that a ∈ ℤ by using h₂.
      have ha : ∃ a' : ℤ, a' = a := by
        specialize h₃ 1
        obtain ⟨n, h₄⟩ := h₂ 1
        obtain ⟨n', h₅⟩ := h₂ (1 - n)
        use n' - n
        simp [<-h₄] at h₅
        simp at h₃ h₄
        nth_rw 2 [h₄] at h₃
        simp
        linarith
      obtain ⟨a', ha⟩ := ha
      -- Setting y = 0 in h₀.
      have h₄ (x : ℤ) := h₀ x 0
      simp at h₄
      -- Show that f(0) = 0 by using h₁ and h₂.
      have h0 : f 0 = 0 := by
        specialize h₄ 0
        rw [h₁] at h₄
        -- Note that f(0) is integer.
        obtain ⟨n, h0⟩ := h₂ 0
        simp at h0
        simp [h0] at h₄ ⊢
        norm_cast at h₄
        omega
      -- Set x = f(y) in h₀.
      have h₅ (y : ℤ) : f (f y) = -a * y := by
        specialize h₀ (f y) y
        simp [h0] at h₀
        linarith only [h₀]
      -- Replace y by f(y) in h₀.
      have h₆ (x y : ℤ) : f (x + a * y) = f x + a * f y := by
        specialize h₀ x (f y)
        simp [h₅] at h₀
        -- Note that f(y) is an integer.
        obtain ⟨n, h₆⟩ := h₂ y
        rw [h₆] at h₀ ⊢
        simp_all
      -- Let n = f(1).
      obtain ⟨n, hn⟩ := h₂ 1
      -- Substitute y = 1 at h₆.
      have h₇ (x : ℤ) : f (x + a) = f x + a * n := by
        specialize h₆ x 1
        simp_all
      -- Further substitute x = 0 to get f(a) = an.
      have h₈ : f a = a * n := by
        specialize h₆ 0 1
        simp_all
      -- Perform induction to show that f(ka) = kan for all k ∈ ℤ.
      have h₉ (k : ℕ) : f (k * a) = k * a * n ∧ f (-k * a) = -k * a * n := by
        induction k with
        | zero =>
          simp [h0]
        | succ k hk =>
          refine ⟨?_, ?_⟩
          . simp
            replace hk := hk.1
            rw [add_mul, one_mul]
            rw [show (k : ℕ) * a = (k * a' : ℤ) by rw [<-ha]; simp] at hk ⊢
            rw [h₇]
            simp at hk ⊢
            rw [hk]
            ring
          . simp
            replace hk := hk.2
            rw [show -k * a = ((-1 + -k) * a' : ℤ) + a by rw [<-ha]; simp; ring, h₇] at hk
            rw [show (-1 + -k) * a = ((-1 + -k) * a' : ℤ) by rw [<-ha]; simp]
            apply eq_sub_of_add_eq at hk
            rw [hk]
            ring
      -- In particular, f(an) = an².
      have h₁₀ : f (a * n) = a * n * n := by
        by_cases h : n ≥ 0
        . -- Suppose n ≥ 0.
          specialize h₉ (n.natAbs)
          -- It is tricky to convert (n.natAbs : ℝ) to (n : ℝ). Normal methods don't work.
          have g₀ : n = n.natAbs := by
            rw [Int.natAbs_of_nonneg h]
          have g₁ := g₀
          rify at g₁
          nth_rw 1 [g₀] at g₁
          have g₂ (m : ℕ) : (m : ℝ) = (m : ℤ) := by
            rfl
          rw [<-g₂] at g₁
          rw [g₁] at h₉
          -- Simplify h₉ using n ≥ 0.
          norm_cast at h₉
          simp [abs_of_nonneg h] at h₉
          rw [mul_comm] at h₉
          rw [h₉.1]
        . -- Suppose n < 0.
          specialize h₉ ((-n).natAbs)
          -- Tricky conversion again.
          have g₀ : -n = (-n).natAbs := by
            rw [Int.natAbs_of_nonneg (by linarith only [h])]
          have g₁ := g₀
          rify at g₁
          have g₂ (z : ℤ) : (-z : ℝ) = (-z : ℤ) := by
            simp
          rw [g₂] at g₁
          nth_rw 1 [g₀] at g₁
          have g₃ (m : ℕ) : (m : ℝ) = (m : ℤ) := by
            rfl
          rw [<-g₃] at g₁
          rw [g₁] at h₉
          norm_cast at h₉
          rw [abs_of_nonneg (by linarith only [h])] at h₉
          simp at h₉
          replace h₉ := h₉.2
          rw [mul_comm] at h₉
          exact h₉
      -- Set y = a in h₅ to get -a² = f(f(n)) = an².
      specialize h₅ a'
      rw [ha] at h₅
      nth_rw 1 [<-h₈] at h₁₀
      use n
      replace h₅ := h₁₀.symm ▸ h₅
      rw [mul_comm _ a, mul_assoc] at h₅
      rw [mul_right_inj' (by positivity)] at h₅
      linarith only [h₅]
  . -- Show that if a = -n² for some n ∈ ℤ, the condition is satisfied.
    rintro ⟨n, h₀⟩
    simp
    -- Use f(x) = n⌊x⌋.
    use λ x => n * ⌊x⌋
    intro x y
    simp [h₀]
    norm_cast
    rw [Int.floor_sub_int]
    ring
