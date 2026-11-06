import Mathlib

/- (Vietnam 2014).

Déterminer toutes les fonctions $f: \mathbb{Z} \mapsto \mathbb{Z}$ telles

$$
f(2 m+f(m)+f(m) f(n))=n f(m)+m
$$

pour tous les entiers $m$ et $n$. -/
theorem algebra_607577 (f : ℤ → ℤ) :
    (∀ m n, f (2 * m + f m + f m * f n) = n * f m + m) ↔ ∀ n, f n = n - 2 := by
  -- Separate the goal into two parts.
  apply Iff.intro
  . -- First show that if the condition holds, then f(n) = n - 2.
    intro h
    -- Substitute m = 0 in h and let c = f(0).
    have h₀ := h 0
    let c := f 0
    simp [show f 0 = c by rfl] at h₀
    by_cases hc : c = 0
    . -- First consider the case c = 0.
      rw [hc] at h₀
      -- Substitute n = 0 in h.
      have h₁ (m : ℤ) := h m 0
      simp [show f 0 = c by rfl, hc] at h₁
      -- Now f is surjective. Let b = 2(-1) + f(-1), so f(b) = -1.
      let b := 2 * (-1) + f (-1)
      have hb : f b = -1 := by
        rw [h₁ (-1)]
      -- Substitute m = n = b in h.
      have h₂ := h b b
      simp [hb] at h₂
      -- Substitute m = b in h to show that f is injective.
      have h₃ : Function.Injective f := by
        intro x y hf
        have hx := h b x
        have hy := h b y
        rw [hf] at hx
        rw [hx, hb] at hy
        linarith
      -- Show that 2b = 0 since f(2b) = f(0).
      rw [<-hc, show c = f 0 by rfl] at h₂
      apply h₃ at h₂
      simp at h₂
      -- Now b = 0 and f(0) = -1, contradiction.
      rw [h₂, show f 0 = c by rfl] at hb
      linarith only [hb, hc]
    . -- Now assume that c ≠ 0.
      -- Show that f is injective.
      have h₁ : Function.Injective f := by
        intro x y hf
        have hx := h₀ x
        have hy := h₀ y
        rw [hf] at hx
        rw [hx] at hy
        rw [mul_left_inj' hc] at hy
        exact hy
      -- Substitute n = 1 in h₀.
      have h₂ := h₀ 1
      nth_rw 3 [show c = f 0 by rfl] at h₂
      rw [one_mul] at h₂
      -- Use injectivity to show that c(1+f(1))=0.
      have h₃ : c * (1 + f 1) = 0 := by
        apply h₁ at h₂
        linarith only [h₂]
      simp [hc] at h₃
      -- Now f(1) = -1.
      replace h₃ : f 1 = -1 := by
        linarith only [h₃]
      -- Substitute n = 1 in h.
      have h₄ (m : ℤ) := h m 1
      simp [h₃] at h₄
      -- Substitute m = 1 in h.
      have h₅ := h 1
      simp [h₃] at h₅
      -- Substitute m = 1 in h₄ to show that f(2) = 0.
      have h₆ := h₄ 1
      simp [h₃] at h₆
      -- Substitute m = 2 in h₄ to show that f(4) = 2.
      have h₇ := h₄ 2
      simp [h₆] at h₇
      -- Substitute n = -1 in h₅ and use injectivity to show f(-1) = -3.
      have h₈ := h₅ (-1)
      simp [<-h₇] at h₈
      apply h₁ at h₈
      replace h₈ : f (-1) = -3 := by
        linarith only [h₈]
      -- Substitute n = -1 in h₀.
      have h₉ := h₀ (-1)
      simp [h₈] at h₉
      rw [show c + -(c * 3) = 2 * -c by ring] at h₉
      -- Substitute m = -c in h₄ and substitute into h₉.
      rw [h₄ (-c)] at h₉
      -- Use injectivity to show that f(0) = c = -2.
      replace h₉ : f (-c) = f 2 := by
        linarith only [h₉, h₆]
      apply h₁ at h₉
      have h₁₀ : f 0 = -2 := by
        linarith only [h₉]
      -- Substitute c = -2 into h₀.
      rw [show c = f 0 by rfl, h₁₀] at h₀
      -- Substitute n = 1 - f(n) in h₀ and simplify it using h₅ to show that f(2n - 4) = 2f(n) - 2.
      have h₁₁ (n : ℤ) : f (2 * n - 4) = 2 * f n - 2 := by
        specialize h₀ (1 + -f n)
        rw [h₅ n] at h₀
        ring_nf at h₀ ⊢
        exact h₀
      -- Use h₄ for n and (n - 2) and combine with h₁₁ to show that f(n - 2) + n = 2f(n).
      have h₁₂ (n : ℤ) : f (n - 2) + n = 2 * f n := by
        have := h₄ (n - 2)
        rw [show 2 * (n - 2) = 2 * n - 4 by ring] at this
        linarith [this, h₄, h₁₁ n]
      -- Show that f(n) = n - 2 for all n ≥ 0.
      have h₁₃ (n : ℕ) : f (2 * n) = 2 * n - 2 ∧ f (2 * n + 1) = 2 * n + 1 - 2 := by
        induction n with
        | zero =>
          simp [h₃, h₁₀]
        | succ n hn =>
          -- Substitute n = 2(n + 1) and n = 2(n + 1) + 1 into h₁₂ respectively.
          have h₁₄ := h₁₂ (2 * (n + 1))
          have h₁₅ := h₁₂ (2 * (n + 1) + 1)
          ring_nf at h₁₄ h₁₅ hn
          rw [hn.1] at h₁₄
          rw [hn.2] at h₁₅
          nth_rw 2 [show (2 + n * 2 : ℤ) = 2 * (n + 1 : ℕ) by norm_cast; ring] at h₁₄
          nth_rw 2 [show (3 + n * 2 : ℤ) = 2 * (n + 1 : ℕ) + 1 by norm_cast; ring] at h₁₅
          rw [show (2 + n * 2 + (-2 + n * 2) : ℤ) = 2 * n * 2 by ring] at h₁₄
          rw [show (3 + n * 2 + (-1 + n * 2) : ℤ) = (2 * n + 1) * 2 by ring] at h₁₅
          rw [mul_left_inj' (by norm_num)] at h₁₄ h₁₅
          -- Substitute the equations derived from induction hypothesis into the goal.
          rw [<-h₁₄, <-h₁₅]
          omega
      replace h₁₃ (n : ℕ) : f n = n - 2 := by
        by_cases hn : Even n
        . -- First consider the case n is even.
          obtain ⟨m, hm⟩ := hn
          rw [hm, <-mul_two, mul_comm]
          push_cast
          exact (h₁₃ m).1
        . -- Now consider the case n is odd.
          simp [Odd] at hn
          obtain ⟨m, hm⟩ := hn
          rw [hm]
          exact (h₁₃ m).2
      -- Now show that f(n) = n - 2 for all integer n.
      have h₁₄ (n : ℤ) : f n = n - 2 := by
        by_cases hn : n ≥ 0
        . -- First consider the case n ≥ 0.
          specialize h₁₃ (n.natAbs)
          zify at h₁₃
          simp [abs_of_nonneg hn] at h₁₃
          exact h₁₃
        . -- Now consider the case n < 0.
          specialize h₁₃ ((3 - n).natAbs)
          zify at h₁₃
          simp [abs_of_nonneg (show 0 ≤ 3 - n by omega)] at h₁₃
          -- Use hypothesis h₅.
          specialize h₅ n
          ring_nf at h₅ h₁₃
          rw [<-h₅] at h₁₃
          -- Use injectivity of f.
          apply h₁ at h₁₃
          linarith
      exact h₁₄
  . -- Now show that if f(n) = n - 2, then the condition holds.
    intro hf m n
    rw [hf, hf, hf]
    ring_nf
