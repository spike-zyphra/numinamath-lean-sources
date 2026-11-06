import Mathlib

theorem number_theory_16494 : {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ ∃ p q : ℕ, (n / 350 : ℝ) = p / 10 ^ q}.encard = 49 := by
  -- Create a bijection between two sets.
  let φ : {n : ℕ | 1 ≤ 7 * n ∧ 7 * n ≤ 349} → {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ ∃ p q : ℕ, (n / 350 : ℝ) = p / 10 ^ q} := fun n ↦ ⟨7 * n, ?_⟩
  pick_goal 2
  -- Show that 7 * n belongs to the set on the right if n belongs to the set on the left, so that φ is a function.
  obtain ⟨n, h₀, h₁⟩ := n
  simp
  refine ⟨?_, ?_, ?_⟩
  . exact h₀
  . exact h₁
  . use (2 * n), 2
    rw [show (350 : ℝ) = 7 * 50 by norm_num, show (10 ^ 2 : ℝ) = 2 * 50 by norm_num, mul_div_mul_left, show (2 * n : ℕ) = (2 : ℝ) * (n : ℕ) by norm_num, mul_div_mul_left]
    norm_num
    norm_num
  -- With bijection φ, the two sets have the same cardinality.
  have h₀ : {n : ℕ | 1 ≤ 7 * n ∧ 7 * n ≤ 349}.encard = {n : ℕ | 1 ≤ n ∧ n ≤ 349 ∧ ∃ p q : ℕ, (n / 350 : ℝ) = p / 10 ^ q}.encard := by
    refine (Set.encard_congr (Equiv.ofBijective φ ⟨fun m n heq ↦ ?_, fun ⟨n, h₀, h₁, p, q, h₂⟩ ↦ ?_⟩))
    . -- Show that φ is injective.
      obtain ⟨m, h₀, h₁⟩ := m
      obtain ⟨n, h₂, h₃⟩ := n
      simp [φ] at heq
      congr
    . -- Show that φ is surjective.
      simp [φ]
      rw [div_eq_div_iff] at h₂
      norm_cast at h₂
      -- Show that 7 ∣ n.
      have h₃ : 7 ∣ n * 10 ^ q := by
        calc
          7 ∣ 350 := by norm_num
          _ ∣ p * 350 := by apply Nat.dvd_mul_left
          _ = n * 10 ^ q := by rw [h₂]
      rw [Prime.dvd_mul] at h₃
      obtain h₃ | wh := h₃
      . -- Normal case.
        apply exists_eq_mul_right_of_dvd at h₃
        obtain ⟨p, h₃⟩ := h₃
        use p
        rw [<-h₃]
        tauto
      . -- Impossible case : 7 ∣ 10 ^ q.
        rw [Prime.dvd_pow_iff_dvd] at wh
        absurd wh
        norm_num
        apply Nat.Prime.prime
        native_decide -- We need the fact that 7 is a prime.
        by_contra!
        rw [this] at h₂
        omega
      apply Nat.Prime.prime
      native_decide -- We need the fact that 7 is a prime.
      norm_num
      apply pow_ne_zero
      norm_num
  have h₁ : {n : ℕ | 1 ≤ 7 * n ∧ 7 * n ≤ 349} = Finset.Icc 1 49 := by
    ext n
    simp
    apply Iff.intro <;> intro h
    . omega
    . omega
  rw [h₀.symm, h₁]
  simp
  have h₂ : (Set.Icc 1 49).ncard = 49 := by
    calc
      (Set.Icc 1 49).ncard = (Finset.Icc 1 49).card := by rw [<-Finset.coe_Icc, Set.ncard_coe_Finset]
      _ = 49 := by apply Nat.card_Icc
  rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, h₂]
  norm_num
  apply Set.finite_of_ncard_pos
  rw [h₂]
  norm_num
