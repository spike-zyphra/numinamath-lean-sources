import Mathlib


lemma nat_div_mul_right_comm {a b : Nat} (hba : b ∣ a) (c : Nat) : a / b * c = a * c / b := by
  rw [Nat.mul_comm, ← Nat.mul_div_assoc _ hba, Nat.mul_comm]


theorem number_theory_635900 {L S : ℕ} (hL : 1 ≤ L) (hS : 1 ≤ S) :
  IsLeast {n | 0 < n ∧ n * S ≡ 0 [MOD L]} (L / Nat.gcd S L) := by


  constructor
  . simp
    have h1 : 0 < S.gcd L := by
      by_contra h
      simp at h
      rw [Nat.gcd_eq_zero_iff] at h
      omega
    refine ⟨⟨h1, ?_⟩, ?_⟩
    . have := Nat.gcd_dvd_right S L
      apply Nat.le_of_dvd hL
      exact this

    . rw [Nat.modEq_zero_iff_dvd]
      rw [nat_div_mul_right_comm (Nat.gcd_dvd_right S L)]
      have := Nat.gcd_mul_lcm L S
      rw [← this]
      rw [Nat.gcd_comm]
      rw [Nat.mul_div_cancel_left]
      . exact Nat.dvd_lcm_left L S
      . exact h1

  . simp [lowerBounds]
    intro n hn hmod

    have hgcd : S.gcd L ≠ 0 := by
      by_contra h
      rw [Nat.gcd_eq_zero_iff] at h
      omega

    obtain ⟨S', hS'⟩ := Nat.gcd_dvd_left S L
    obtain ⟨L', hL'⟩ := Nat.gcd_dvd_right S L
    have h1 : Nat.gcd S' L' = 1 := by
      have : S.gcd L = S.gcd L := by rfl
      nth_rw 1 [hS'] at this
      nth_rw 2 [hL'] at this
      rw [Nat.gcd_mul_left] at this
      nlinarith

    rw [hS'] at hmod
    nth_rw 1 [hL'] at hmod
    rw [← mul_assoc] at hmod
    rw [mul_comm n (S.gcd L)] at hmod
    rw [mul_assoc] at hmod
    have h2: n * S' ≡ 0 [MOD L'] := @Nat.ModEq.mul_left_cancel' (n * S') 0 (S.gcd L) L' hgcd (by simp; exact hmod)

    have h3 : L' ∣ n := by
      apply @Nat.Coprime.dvd_of_dvd_mul_right L' S' n
      . unfold Nat.Coprime
        rw [Nat.gcd_comm]
        exact h1
      . rw [Nat.modEq_zero_iff_dvd] at h2
        exact h2

    apply Nat.le_of_dvd hn at h3
    have : L' = L / (S.gcd L) := by
      nth_rw 1 [hL']
      rw [Nat.mul_div_cancel_left]
      omega


    rw [this] at h3
    exact h3
