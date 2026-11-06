import Mathlib

/- Let $p_{1}<p_{2}<p_{3}<p_{4}$ and $q_{1}<q_{2}<q_{3}<q_{4}$ be two sets of prime numbers such that $p_{4}-p_{1}=8$ and $q_{4}-q_{1}=8$. Suppose $p_{1}>5$ and $q_{1}>5$. Prove that 30 divides $p_{1}-q_{1}$. -/
lemma prime_tuples_helper
  {p₁ p₂ p₃ p₄ : ℕ}
  (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
  (hp₃ : Nat.Prime p₃) (hp₄ : Nat.Prime p₄)
  (hp_ordered : p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄)
  (hp_diff : p₄ - p₁ = 8)
  (hp₁_gt_5 : p₁ > 5)
    : p₁ ≡ 11 [MOD 30] := by

  have hp₁_odd : p₁ % 2 = 1 := by
    have := Fact.mk hp₁
    rw [Nat.Prime.mod_two_eq_one_iff_ne_two]
    exact ne_of_gt (gt_of_gt_of_ge hp₁_gt_5 (by norm_num))

  let s : Finset ℕ := { p₁+2, p₁+4, p₁+6 }
  replace hp_diff : p₄ = p₁ + 8 := by omega

  have h₂ : ∀ p : ℕ, Odd p → p₁ < p ∧ p < p₄ →
      p ∈ s := by
    rintro p hp ⟨p_gt_p₁, p_lt_p₄⟩
    rw [hp_diff] at p_lt_p₄
    suffices p - p₁ ∈ {2, 4, 6} by
      have : s = Finset.image (· + p₁) {2, 4, 6} := by
        simp [s, add_comm]
      rw [this]
      have := Finset.mem_image (b := p) (s := ({2, 4, 6} : Finset ℕ) ) (f := (· + p₁))
      rw [this]
      use p - p₁
      constructor
      · assumption
      · omega

    simp
    have : Even (p - p₁) :=
      Nat.Odd.sub_odd hp (Nat.odd_iff.mpr hp₁_odd)
    have : p - p₁ < 8 := by omega
    have : 0 < p - p₁ := by omega
    interval_cases p - p₁
    any_goals
      subst hp_diff
      simp_all [Nat.not_even_iff]
    all_goals
      have : ¬Even 3 := by exact Nat.not_even_iff.mpr rfl
      have : ¬Even 5 := by exact Nat.not_even_iff.mpr rfl
      have : ¬Even 7 := by exact Nat.not_even_iff.mpr rfl
      simp_all

  have h₃ : p₂ ∈ s ∧ p₃ ∈ s
    := by
    constructor
    · exact @h₂ p₂ (Nat.Prime.odd_of_ne_two hp₂ (by omega)) (by omega)
    · exact @h₂ p₃ (Nat.Prime.odd_of_ne_two hp₃ (by omega)) (by omega)

  have h₄ : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ Nat.Prime x ∧ Nat.Prime y := by
    aesop

  have h₅ : ¬p₁ ≡ 1 [MOD 3] := by
    intro p₁_congr
    have : p₁ + 8 ≡ 0 [MOD 3] := by
      have := @Nat.ModEq.add 3 p₁ 1 8 2 p₁_congr (by rfl)
      exact this

    have : ¬Nat.Prime (p₁ + 8) := by
      intro hp
      have : 3 ∣ (p₁ + 8) := Nat.dvd_of_mod_eq_zero this
      rw [@Nat.dvd_prime_two_le (p₁ + 8) 3 hp (by simp)] at this
      linarith

    have : ¬ Nat.Prime (p₄) := by
      exact Eq.mpr_not (congrArg Nat.Prime hp_diff) this

    contradiction

  have h₆ : p₁ ≡ 2 [MOD 3] := by
    mod_cases hmod : p₁ % 3
    · have : 3 ∣ p₁ := by exact Nat.dvd_of_mod_eq_zero hmod
      rw [@Nat.dvd_prime_two_le p₁ 3 hp₁ (by simp)] at this
      linarith
    · exact False.elim (h₅ hmod)
    · exact hmod

  have h₇ : ¬Nat.Prime (p₁ + 4) := by
    intro hp
    have : p₁ + 4 ≡ 0 [MOD 3] := by
      have : p₁ + 4 ≡ 2 + 4 [MOD 3] := Nat.ModEq.add_right 4 h₆
      simpa using this

    have : 3 ∣ p₁ + 4 := by exact Nat.dvd_of_mod_eq_zero this
    rw [@Nat.dvd_prime_two_le (p₁ + 4) 3 hp (by simp)] at this
    linarith

  have h₈ : p₂ = p₁ + 2 ∧ p₃ = p₁ + 6 := by
    have : p₂ = p₁ + 2 ∨ p₂ = p₁ + 4 := by
      aesop
    have : p₃ = p₁ + 4 ∨ p₃ = p₁ + 6 := by
      have : p₃ =  p₁ + 2 ∨ p₃ = p₁ + 4 ∨ p₃ = p₁ + 6 := by
        simp [s] at h₃
        omega
      omega

    aesop

  have h₉ : ¬p₁ ≡ 2 [MOD 5]:= by
    intro p_congr
    have : p₁ + 8 ≡ 0 [MOD 5] := by
      simpa using Nat.ModEq.add_right 8 p_congr
    have : 5 ∣ p₁ + 8 := by exact Nat.dvd_of_mod_eq_zero this
    rw [<- hp_diff] at this
    rw [@Nat.dvd_prime_two_le p₄ 5 hp₄ (by simp)] at this
    linarith

  have h₁₀ : ¬p₁ ≡ 3 [MOD 5] := by
    intro p_congr
    have : p₁ + 2 ≡ 0 [MOD 5] := by
      simpa using Nat.ModEq.add_right 2 p_congr
    have : 5 ∣ p₁ + 2 := by exact Nat.dvd_of_mod_eq_zero this
    rw [<- h₈.left] at this
    rw [@Nat.dvd_prime_two_le p₂ 5 hp₂ (by simp)] at this
    linarith

  have h₁₁ : ¬p₁ ≡ 4 [MOD 5] := by
    intro p_congr
    have : p₁ + 6 ≡ 0 [MOD 5] := by
      simpa using Nat.ModEq.add_right 6 p_congr
    have : 5 ∣ p₁ + 6 := by exact Nat.dvd_of_mod_eq_zero this
    rw [<- h₈.right] at this
    rw [@Nat.dvd_prime_two_le p₃ 5 hp₃ (by simp)] at this
    linarith

  have h₁₂ : p₁ ≡ 1 [MOD 5] := by
    mod_cases p₁ % 5 <;>
      simp_all
    have : 5 ∣ p₁ := by exact Nat.dvd_of_mod_eq_zero H
    rw [@Nat.dvd_prime_two_le p₁ 5 hp₁ (by simp)] at this
    omega

  have h₁₃ : p₁ ≡ 1 [MOD 2] := by
    exact hp₁_odd

  have hmul6 := by simpa using Nat.ModEq.mul_left' 6 h₁₂
  have hmul10 := by simpa using Nat.ModEq.mul_left' 10 h₆
  have hmul15 := by simpa using Nat.ModEq.mul_left' 15 h₁₃
  have := by
    have := Nat.ModEq.add hmul10 hmul6
    exact Nat.ModEq.add this hmul15
  ring_nf at this
  rw [mul_comm] at this
  exact Nat.ModEq.cancel_left_of_coprime (by rfl) this



theorem number_theory_607857
  (p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : ℕ)
  (h_ord : q₁ ≤ p₁)
  (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hp₃ : Nat.Prime p₃) (hp₄ : Nat.Prime p₄)
  (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂) (hq₃ : Nat.Prime q₃) (hq₄ : Nat.Prime q₄)
  (hp_ordered : p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄)
  (hq_ordered : q₁ < q₂ ∧ q₂ < q₃ ∧ q₃ < q₄)
  (hp_diff : p₄ - p₁ = 8)
  (hq_diff : q₄ - q₁ = 8)
  (hp₁_gt_5 : p₁ > 5)
  (hq₁_gt_5 : q₁ > 5) :
    30 ∣ p₁ - q₁ := by

  have h₁₄ : p₁ ≡ 11 [MOD 30] := by
    exact prime_tuples_helper hp₁ hp₂ hp₃ hp₄ hp_ordered hp_diff hp₁_gt_5

  have h₁₅ : q₁ ≡ 11 [MOD 30] := by
    exact prime_tuples_helper hq₁ hq₂ hq₃ hq₄ hq_ordered hq_diff hq₁_gt_5

  have h₃ : (30 : ℤ) ∣ (11 - q₁ - (11 - p₁)) := Int.dvd_sub h₁₅.dvd h₁₄.dvd
  simp at h₃
  exact_mod_cast h₃
  