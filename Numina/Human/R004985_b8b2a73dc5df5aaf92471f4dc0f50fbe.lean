import Mathlib

/- Es sei $\mathbb{Z}^{+}$die Menge der positiven ganzen Zahlen.
Man bestimme alle Funktionen $f: \mathbb{Z}^{+} \rightarrow \mathbb{Z}^{+}$mit der Eigenschaft, dass für alle positiven ganzen Zahlen $m$ und $n$ gilt: $m^{2}+f(n) \mid m f(m)+n$. -/
theorem number_theory_604935 :
    {f : ℕ → ℕ | (∀ n, 0 < n → 0 < f n) ∧ ∀ m n, 0 < m → 0 < n → m ^ 2 + f n ∣ m * f m + n} = {f : ℕ → ℕ | ∀ n, 0 < n → f n = n} := by
  -- Break the goal into two parts.
  ext f
  simp
  constructor
  . -- Show that f(n) = n is the only possible solution.
    rintro ⟨h₀, h₁⟩
    -- We first show that f(n) ∣ n for all n > 0.
    have h₂ (n : ℕ) (hn : 0 < n) : f n ∣ n := by
      -- Substitute m = f(n) into the original condition.
      specialize h₁ (f n) n (h₀ n hn) hn
      -- We have f(n) ∣ f(n)f(f(n)) + n, and hence f(n) ∣ n.
      have h₃ : f n ∣ f n * f (f n) + n := by
        calc
          _ ∣ f n ^ 2 + f n := by
            rw [pow_two, <-Nat.mul_succ]
            apply dvd_mul_right
          _ ∣ f n * f (f n) + n := h₁
      rw [<-Nat.dvd_add_iff_right (by apply dvd_mul_right)] at h₃
      exact h₃
    by_cases h₃ : ∃ c > 0, ∀ n > 0, f n = c
    . -- Assume that f is a constant function, we should derive a contradiction.
      exfalso
      obtain ⟨c, hc, h₃⟩ := h₃
      -- Substitute (m, n) = (1, 2) into the original condition.
      specialize h₁ 1 2 (by norm_num) (by norm_num)
      simp [h₃] at h₁
      rw [show c + 2 = (1 + c) + 1 by ring, <-Nat.dvd_add_iff_right (by rfl)] at h₁
      simp at h₁
      linarith
    . -- Now f cannot be a constant function.
      by_cases h₄ : ∀ n > 0, f n = n
      . -- Suppose f(n) = n for all n > 0, then we are done.
        exact h₄
      . -- Suppose f(n) ≠ n for some n, we take some k such that f(k) < k.
        simp at h₄
        obtain ⟨k, hk, h₄⟩ := h₄
        replace h₄ := lt_of_le_of_ne (Nat.le_of_dvd hk (h₂ k hk)) h₄
        -- Let d = f(k).
        set d := f k with hd
        -- Let k = cd for some c > 0.
        have hc := h₂ k hk
        rw [dvd_iff_exists_eq_mul_left] at hc
        obtain ⟨c, hc⟩ := hc
        have hc' : c ≥ 2 := by
          nlinarith
        have hd' : d > 0 := by
          nlinarith
        rw [<-hd] at hc
        -- Show that dc² + 1 ∣ (d + 1)c.
        specialize h₁ k k (by positivity) (by positivity)
        rw [<-hd, hc, show (c * d) ^ 2 + d = (d * c ^ 2 + 1) * d by ring, show c * d * d + c * d = (d + 1) * c * d by ring] at h₁
        apply Nat.dvd_of_mul_dvd_mul_right (by positivity) at h₁
        -- Show that dc² + 1 ∣ -(dc² - cd) + (c - 1).
        have h₅ : (d * c ^ 2 + 1 : ℤ) ∣ -(d * c ^ 2 - c * d : ℤ) + (c - 1) := by
          rw [<-@Int.dvd_add_left _ _ (d * c ^ 2 + 1) (by rfl)]
          ring_nf at h₁ ⊢
          norm_cast at h₁ ⊢
        -- Show that dc² + 1 ≤ cd + c ≤ dc² + c.
        have h₆ : d * c ^ 2 + 1 ≤ c * d + c ∧ c * d + c ≤ d * c ^ 2 + c := by
          refine ⟨?_, ?_⟩
          . -- Show that dc² + 1 ≤ cd + c.
            ring_nf at h₁ ⊢
            apply Nat.le_of_dvd (by positivity) h₁
          . -- Show that cd + c ≤ dc² + c.
            calc
              _ ≤ c * (c * d) + c := by
                simp
                apply Nat.mul_le_mul_left
                apply Nat.le_of_dvd (by positivity)
                apply dvd_mul_left
              _ = d * c ^ 2 + c := by
                ring
        rw [<-Int.dvd_natAbs] at h₅
        norm_cast at h₅
        zify at h₆
        by_cases h₇ : d * c ^ 2 + 1 = c * (d) + c
        . -- Suppose dc² + 1 = cd + c, we shall derive a contradiction.
          have h₈ : c ∣ d * c ^ 2 + 1 := by
            rw [h₇, <-Nat.mul_succ]
            apply dvd_mul_right
          rw [<-Nat.dvd_add_iff_right (by rw [pow_two, <-mul_assoc]; apply dvd_mul_left)] at h₈
          norm_num at h₈
          omega
        . -- Suppose dc² + 1 < cd + c, we also derive a contradiction.
          iterate 2 rw [Int.subNatNat_eq_coe] at h₅
          apply Nat.le_of_dvd (by simp; contrapose! h₇; linarith) at h₅
          zify at h₅
          have h₈ : c < c := by
            zify
            calc
              _ < (d * c ^ 2 + 1 : ℤ) := by
                nlinarith
              _ ≤ |-(d * c ^ 2 - c * d : ℤ) + (c - 1)| := h₅
              _ ≤ c - 1 := by
                rw [abs_of_nonneg (by linarith)]
                linarith
              _ < c := by
                linarith
          absurd h₈
          simp
  . -- Show that f(n) = n satisfies the condition.
    intro h₀
    refine ⟨?_, ?_⟩
    . -- Verify that f(n) > 0 for n > 0.
      intro n hn
      rw [h₀ n hn]
      exact hn
    . -- Show that the condition holds for all m, n > 0.
      intro m n h₁ h₂
      rw [h₀ m h₁, h₀ n h₂]
      ring_nf
      rfl
