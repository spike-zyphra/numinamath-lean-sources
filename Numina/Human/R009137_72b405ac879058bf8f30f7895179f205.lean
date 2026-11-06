import Mathlib

/- On note $\mathbb{N}^{*}$ l'ensemble des entiers naturels strictement positifs. Trouver toutes les $^{2}$ fonctions $f: \mathbb{N}^{*} \rightarrow \mathbb{N}^{*}$ telles que

$$
m^{2}+f(n) \mid m f(m)+n
$$

pour tous entiers strictement positifs $m$ et $n$. -/
theorem number_theory_604784 :
    {f : ℕ+ → ℕ+ | ∀ m n, m ^ 2 + f n ∣ m * f m + n} = {id} := by
  -- Break the goal into two parts.
  ext f
  simp
  apply Iff.intro
  . -- First show that the given condition implies that f is identity function.
    intro h₀
    -- First determine f(2) by setting m = 2 and n = 2.
    have h₁ : 2 ^ 2 + f 2 ∣ 2 * f 2 + 2 := by
      apply h₀
    rw [PNat.dvd_iff, dvd_iff_exists_eq_mul_left] at h₁
    obtain ⟨c, h₁⟩ := h₁
    -- We must not have c ≥ 2.
    have h₂ : c < 2 := by
      by_contra! h₂
      have habsurd : (2 * f 2 + 2 : ℕ) > 2 * f 2 + 2 := by
        calc
          2 * f 2 + 2 = c * (2 ^ 2 + f 2) := h₁
          _ ≥ 2 * (2 ^ 2 + f 2) := by rw [ge_iff_le, mul_le_mul_right (by positivity)]; exact h₂
          _ > 2 * f 2 + 2 := by omega
      absurd habsurd
      simp
    -- We must not have c = 0.
    have h₃ : c ≠ 0 := by
      intro h₃
      simp [h₃] at h₁
    -- So we have c = 1 and f(2) = 2.
    simp [show c = 1 by omega] at h₁
    replace h₁ : (f 2 : ℕ) = 2 := by
      linarith
    clear h₂ h₃
    -- Substitute m = 2 into the original divisibility condition.
    have h₂ : ∀ n, 4 + f n ∣ 4 + n := by
      intro n
      specialize h₀ 2 n
      simp [PNat.dvd_iff] at h₀ ⊢
      rw [h₁] at h₀
      exact h₀
    -- We have f(n) ≤ n for all n.
    replace h₂ : ∀ n, f n ≤ n := by
      intro n
      have h₂ : 4 + f n ≤ 4 + n := PNat.le_of_dvd (h₂ n)
      rw [<-PNat.coe_le_coe] at h₂ ⊢
      rw [PNat.add_coe, PNat.add_coe] at h₂
      omega
    -- We have f(n) ≥ n for all n.
    have h₃ : ∀ n, f n ≥ n := by
      intro n
      -- Substitute m = n into the original divisibility condition.
      specialize h₀ n n
      rw [PNat.dvd_iff] at h₀
      apply Nat.le_of_dvd (by positivity) at h₀
      -- We have (n - 1)(f(n) - n) ≥ 0.
      replace h₀ : (n - 1) * (f n - n) ≥ (0 : ℤ) := by
        rw [PNat.add_coe, PNat.add_coe] at h₀
        linarith
      by_cases hn : n ≤ 1
      . -- If n ≤ 1, then f(n) ≥ n.
        exact hn.trans (show 1 ≤ f n by simp)
      . -- If n > 1, we have f(n) - n ≥ 0 because (n - 1)(f n - n) ≥ 0.
        rw [ge_iff_le] at h₀
        replace hn : 1 < n := by
          by_contra!
          contradiction
        rw [<-PNat.coe_lt_coe] at hn
        rw [mul_nonneg_iff_of_pos_left (by simp_all)] at h₀
        simp at h₀
        apply h₀
    -- Now we have f(n) = n for all n.
    ext n
    simp
    exact le_antisymm (h₂ n) (h₃ n)
  . -- Show that the identity function does satisfy the given condition.
    intro h₀
    simp [h₀, <-pow_two]
