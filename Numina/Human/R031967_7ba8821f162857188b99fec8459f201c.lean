import Mathlib

/- Problem 4. Prove that the fraction $\frac{a^{2}+3}{a^{4}+7 a^{2}+11}$ is irreducible for every integer $a$. -/

theorem number_theory_234838 (a : ℤ) :
    IsCoprime (a^2 + 3) (a^4 + 7 * a^2 + 11) := by

      --Rewrite a^4 + 7 * a^2 + 11 = (a^2 + 3)^2 + (a^2 + 3) - 1.
      have h0 : a^4 + 7 * a^2 + 11 = (a^2 + 3)^2 + (a^2 + 3) - 1 := by ring
      rw [h0]

      --Show that any common divisor of (a^2 + 3) and (a^4 + 7 * a^2 + 11) equals -1 or 1.
      have h2 : ∀ k : ℤ, k ∣ (a^2 + 3) → k ∣ ((a^2 + 3)^2 + (a^2 + 3) - 1) → k = 1 ∨ k = -1 := by
        intro k
        intros h1 h2
        rcases h1 with ⟨m, h11⟩
        rcases h2 with ⟨n, h21⟩
        rw [h11] at h21
        have h3 : 1 = (k * m)^2 + k * m - k * n := by linarith
        have h4 : k ∣ (k * m)^2 + k * m - k * n := by
          use k * m^2 + m - n ; linarith
        have h5 : k ∣ 1 := by rw [h3]; exact h4
        rcases h5 with ⟨q, h51⟩
        apply Int.eq_one_or_neg_one_of_mul_eq_one
        exact id (Eq.symm h51)

      --Coprime iff gcd equals one.
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_

      --Let d be the gcd.
      set d := gcd (a^2 + 3) ((a^2 + 3)^2 + (a^2 + 3) - 1)

      --Show d divides a^2 + 3.
      have h31 : d ∣ (a^2 + 3) := by
          exact gcd_dvd_left (a ^ 2 + 3) ((a ^ 2 + 3) ^ 2 + (a ^ 2 + 3) - 1)

      --Show d divides (a^2 + 3)^2 + (a^2 + 3) - 1.
      have h32 : d ∣ ((a^2 + 3)^2 + (a^2 + 3) - 1) := by
          exact gcd_dvd_right (a ^ 2 + 3) ((a ^ 2 + 3) ^ 2 + (a ^ 2 + 3) - 1)

      --Now apply h2 with d and get d equals -1 or 1.
      have h33 : d = 1 ∨ d = -1 := h2 d h31 h32

      --Finish the proof. At this point `apply?` works.
      cases h33 with
      | inl h331 => exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h331)))
      | inr h332=>
          have : 0 ≤ d :=  by exact Int.le.intro_sub ((a ^ 2 + 3).gcd ((a ^ 2 + 3) ^ 2 + (a ^ 2 + 3) - 1) + 0) rfl
          linarith [h332]