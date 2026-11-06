import Mathlib

open Nat

theorem number_theory_8861 (n : ℕ) (hnpos : n > 0) :
    (n ! + 1).gcd (n + 1)! = if (n + 1).Prime then n + 1 else 1 := by
  split_ifs with hn
  . have H₁ : n + 1 ∣ n ! + 1 := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
      simp [show n ! = (-1 : ZMod (n + 1)) from @ZMod.wilsons_lemma (n + 1) ⟨hn⟩]
    have H₂ : (n !).Coprime (n ! + 1) := coprime_self_add_right.mpr (Nat.gcd_one_right _)
    rw [gcd_comm, factorial_succ, mul_comm, gcd_mul_of_coprime_of_dvd H₂ H₁]
  . refine coprime_of_dvd' fun p hp h₁ h₂ => ?_
    have H₁ : p ≠ n + 1 := fun h => hn (h ▸ hp)
    rw [Prime.dvd_factorial hp, Nat.le_add_one_iff, or_iff_left H₁, ← Prime.dvd_factorial hp] at h₂
    exact (Nat.dvd_add_iff_right h₂).mpr h₁
