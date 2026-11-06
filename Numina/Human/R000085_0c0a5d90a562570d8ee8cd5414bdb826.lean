import Mathlib

/- Show that there are no "prime triplets", i.e., sets of three prime numbers of the form
  \( p, p+2, \) and \( p+4 \), other than the triplet \( 3, 5, \) and \( 7 \). -/
theorem number_theory_4495 (p : ℕ) :
    p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime → p = 3 := by
  intro ⟨h₁, h₂, h₃⟩
  by_contra hp
  -- split into three cases, two of them are trivial.
  have hp' : p < 2 ∨ p = 2 ∨ p > 3 := by omega
  rcases hp' with hp' | hp' | hp'
  · simpa using lt_of_le_of_lt (Nat.Prime.two_le h₁) hp'
  · rw [hp'] at h₂
    absurd h₂
    decide
  · have three_not_div {q : ℕ} (hq : q.Prime) (lt : 3 < q) : (q : ZMod 3) ≠ 0 := by
      intro h
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h
      exact Nat.not_prime_of_dvd_of_lt h (by simp) lt hq
    have zmod_ne {q n : ℕ} (hq : (q : ZMod 3) ≠ n) : q % 3 ≠ n := by
      contrapose hq
      simp only [ne_eq, Decidable.not_not] at hq ⊢
      apply_fun Nat.cast (R := ZMod 3) at hq
      simpa using hq
    replace h₁ := three_not_div h₁ hp'
    replace h₂ := three_not_div h₂ (by omega)
    replace h₃ := three_not_div h₃ (by omega)
    simp only [Nat.cast_add, Nat.cast_ofNat] at h₂ h₃
    -- The congruence class of `p` in 3 is neither 0, 1 or 2, which is impossible.
    replace h₁ : p % 3 ≠ 0 := zmod_ne h₁
    replace h₂ : p % 3 ≠ 1 := by apply zmod_ne; intro h; absurd h₂; rw [h]; decide
    replace h₃ : p % 3 ≠ 2 := by apply zmod_ne; intro h; absurd h₃; rw [h]; decide
    have : p % 3 < 3 := by apply Nat.mod_lt; simp
    -- Use `omega` to deduce a contradiction
    omega
