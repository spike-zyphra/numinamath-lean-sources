import Mathlib


/-Let $p$ be the largest prime with 2010 digits. What is the smallest positive integer $k$ such that $p^2 - k$ is divisible by 12?-/
theorem number_theory_16009 {p : ℕ} (hp₁ : Nat.Prime p) (hp₂ : (Nat.digits 10 p).length = 2010) :
    IsLeast {k : ℕ | 0 < k ∧ 12 ∣ p^2 - k } 1 := by
  have : ∃s, s = {k | 0 < k ∧ 12 ∣ p ^ 2 - k } := by simp
  rcases this with ⟨s, hs⟩
  have one_lt_p : 1 < p ^ 2 := by exact Nat.one_lt_pow (by norm_num) (Nat.Prime.one_lt hp₁)

  have one_in_s : 1 ∈ s := by
    rw [hs]
    simp
    -- p^2-1 = (p+1)(p-1)
    have pOdd : Odd p := by
      apply Nat.Prime.odd_of_ne_two
      exact hp₁
      by_contra!
      rw [this] at hp₂
      simp at hp₂
    have dvd4 : 4 ∣ (p + 1) * (p - 1 : ℤ) := by
      have : (4 : ℤ) = 2 * 2 := by norm_num
      rw [this]
      apply mul_dvd_mul
      . -- 2 | (p + 1)
        apply Even.exists_two_nsmul
        apply Int.even_add'.mpr
        simp
        norm_cast
      . -- 2 | (p - 1)
        apply Even.exists_two_nsmul
        apply Int.even_sub'.mpr
        simp
        norm_cast
    have break_down: p^2 - 1 = (p + 1) * (p - 1 : ℤ) := by ring_nf
    rw [break_down.symm] at dvd4
    -- Also, since $p$ is not divisible by 3, then $p$ must either be one greater or two greater than a multiple of 3,
    -- which means that $p-1$ or $p+1$ is divisible by 3,
    have emod_three_eq_zero_or_one_or_two (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
      have h : n % 3 < 3 :=  by omega
      have h₁ : 0 ≤ n % 3 := Int.emod_nonneg _ (by decide)
      match n % 3, h, h₁ with
      | (0 : ℕ), _ ,_ => Or.inl rfl
      | (1 : ℕ), _ ,_ => Or.inr (Or.inl rfl)
      | (2 : ℕ), _ ,_ => Or.inr (Or.inr rfl)
      | (k + 2 : ℕ), h₁, _ => by omega
      | Int.negSucc a, _, h₁ => by cases h₁
    rcases emod_three_eq_zero_or_one_or_two p with (h1 | h2 | h3)
    . -- ↑p % 3 = 0
      norm_cast at h1
      absurd Nat.dvd_of_mod_eq_zero h1
      apply (Nat.Prime.coprime_iff_not_dvd (by norm_cast)).mp
      apply (Nat.coprime_primes (by norm_cast) hp₁).mpr
      intro hp
      rw [hp.symm] at hp₂
      simp at hp₂
    -- respectively. As a result, $p^2-1$ is divisible by both 3 and 4, so it is divisible by 12. Therefore, we have $\boxed{k = 1}$.
    . -- ↑p % 3 = 1
      -- so, 3 ∣ (p - 1)
      have : 3 ∣ (p - 1 : ℤ) := by exact Int.dvd_sub_of_emod_eq h2
      have dvd3 : 3 ∣ (p ^ 2 - 1 : ℤ) := by
        rw [break_down]
        exact Dvd.dvd.mul_left this (↑p + 1)
      have : 12 = lcm 3 4 := by decide
      rw [this]
      have := Int.ofNat_sub one_lt_p.le
      apply lcm_dvd
      norm_cast at this dvd3
      rw [this.symm] at dvd3
      exact Int.ofNat_dvd.mp dvd3
      norm_cast at this dvd4
      rw [this.symm] at dvd4
      exact Int.ofNat_dvd.mp dvd4
    . -- ↑p % 3 = 2
      -- so, 3 ∣ (p + 1)
      norm_cast at h3
      have h3 : p ≡ 2 [MOD 3] := by exact h3
      have : p + 1 ≡ 2 + 1 [MOD 3] := by
        exact Nat.ModEq.add_right 1 h3
      rw [Nat.ModEq] at this
      simp at this
      have : 3 ∣ (p + 1 : ℤ) := by
        apply Int.dvd_of_emod_eq_zero
        norm_cast
      have dvd3 : 3 ∣ (p ^ 2 - 1 : ℤ) := by
        rw [break_down]
        exact Dvd.dvd.mul_right this (↑p - 1)
      have : 12 = lcm 3 4 := by decide
      rw [this]
      have := Int.ofNat_sub one_lt_p.le
      apply lcm_dvd
      norm_cast at this dvd3
      rw [this.symm] at dvd3
      exact Int.ofNat_dvd.mp dvd3
      norm_cast at this dvd4
      rw [this.symm] at dvd4
      exact Int.ofNat_dvd.mp dvd4


  rw [hs.symm]
  unfold IsLeast
  constructor
  . exact one_in_s
  refine (le_csInf_iff' ?intro.right.hs).mp ?intro.right.a
  exact Set.nonempty_of_mem one_in_s

  -- we need to prove  1 ≤ sInf s, but, we can prove that, s ⊆ {k | k > 0}
  have : ∃s', s' = {k | k > 0} := by simp
  rcases this with ⟨s', hs'⟩
  have : s ⊆ s' := by
    rw [hs, hs']
    exact Set.sep_subset (Nat.succ 0).le fun x ↦ 12 ∣ p ^ 2 - x
  -- then, sInf s' ≤ sInf s, and, 1 = sInf s' is true
  have : 1 ≤ sInf s' := by
    apply le_csInf
    exact Set.nonempty_of_mem (this one_in_s)
    rw [hs']
    simp
    intro b
    intro hb
    linarith
  apply le_trans
  exact this
  have : sInf s' ≤ sInf s := by
    apply csInf_le_csInf
    simp
    exact Set.nonempty_of_mem one_in_s
    rw [hs, hs']
    exact Set.sep_subset (Nat.succ 0).le fun x ↦ 12 ∣ p ^ 2 - x
  exact this
