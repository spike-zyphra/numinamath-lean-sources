import Mathlib

theorem number_theory_287853 (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k = ∑ i ∈ Finset.Icc 1 (p - 1), i) :
    k ∣ (p - 1).factorial - (p - 1) := by
  have hp₁ : 1 ≤ p := Nat.Prime.one_le hp
  have hp₂ : 2 ≤ p := Nat.Prime.two_le hp
  have h₁ : (∑ i ∈ Finset.Icc 1 (p - 1), (i : ℤ)) * 2 = p * (p - 1) := by
    clear k hk hp hp₂
    induction p, hp₁ using Nat.le_induction with
    | base => simp
    | succ p hp₁ ih =>
      rw [show p + 1 - 1 = p - 1 + 1 by omega, Finset.sum_Icc_succ_top (by omega), add_mul, ih]
      zify
      simp [show 1 ≤ p by omega]
      ring
  zify
  simp [Nat.self_le_factorial (p - 1), hp₁]
  suffices H : (p * (p - 1) : ℤ) ∣ ((p - 1).factorial - (p - 1) : ℤ) by
    refine dvd_trans ⟨2, ?_⟩ H
    rw [hk]
    zify
    rw [h₁]
  have h₂ : IsCoprime (p : ℤ) (p - 1) := ⟨1, -1, by ring⟩
  apply IsCoprime.mul_dvd h₂
  . rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    -- Wilson's theorem is used to simplify the expression
    simp [show Fact p.Prime from { out := hp }]
  . rw [dvd_sub_self_right,
        show (p - 1 : ℤ) = (p - 1 : ℕ) by simp [hp₁]]
    norm_cast
    refine Nat.dvd_factorial (by omega) (by simp)
