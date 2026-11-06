import Mathlib

lemma pow_mod_10_eq_0_of_mod_10_eq_0 : ∀n ≥ 1,∀m ≥ 1, n % 10 = 0 → n^m % 10 = 0 := by
  intro n hn₁ m hm₁ hn₂
  obtain ⟨k, hn₃⟩ := show ∃k, n = 10 * k by
    use n / 10
    omega
  rw [hn₃, Nat.pow_mod]
  norm_num
  rw [zero_pow]
  simp
  omega

lemma pow_mod_10_eq_1_of_mod_10_eq_1 : ∀n ≥ 1, ∀m ≥ 1, n % 10 = 1 → n^m % 10 = 1 := by
  intro n hn₁ m hm₁ hn₂
  obtain ⟨k, hn₃⟩ := show ∃k, n = 10 * k + 1 by
    use n / 10
    omega
  rw [hn₃, Nat.pow_mod, show (10 * k + 1) % 10 = 1 by omega]
  norm_num

lemma pow_mod_10_eq_5_of_mod_10_eq_5 : ∀n ≥ 1, ∀m ≥ 1, n % 10 = 5 → n^m % 10 = 5 := by
  intro n hn₁ m hm₁ hn₂
  obtain ⟨k, hn₃⟩ := show ∃k, n = 10 * k + 5 by
    use n / 10
    omega
  rw [hn₃, Nat.pow_mod, show (10 * k + 5) % 10 = 5 by omega]
  suffices 10 ∣ 5^m - 5 by
    obtain ⟨p, hp⟩ := this
    have : 5^m = 10 * p + 5 := by
      rw [←hp, Eq.comm]
      apply Nat.sub_add_cancel
      apply Nat.le_self_pow ?_ 5
      omega
    rw [this]
    omega
  have : 5^m - 5 = 5 * (5^(m - 1) - 1) := by
    rw [Nat.mul_sub, mul_comm, ←Nat.pow_add_one]
    rw [show m - 1 + 1 = m by omega]
  rw [this, show 10 = 5 * 2 by norm_num]
  apply Nat.mul_dvd_mul_left 5
  suffices Even (5^(m - 1) - 1) by exact even_iff_two_dvd.mp this
  rw [Nat.even_sub']
  norm_num
  apply Odd.pow
  native_decide
  exact Nat.one_le_pow' (m - 1) 4

lemma pow_mod_10_eq_6_of_mod_10_eq_6 : ∀n ≥ 1, ∀m ≥ 1, n % 10 = 6 → n^m % 10 = 6 := by
  intro n hn₁ m hm₁ hn₂
  obtain ⟨k, hn₃⟩ := show ∃k, n = 10 * k + 6 by
    use n / 10
    omega
  rw [hn₃, Nat.pow_mod, show (10 * k + 6) % 10 = 6 by omega]
  induction' m using Nat.strongRec with m hm
  by_cases hm₂ : m = 1
  · rw [hm₂]
  specialize hm (m - 1) (by omega) (by omega)
  rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod, hm]

/-Define a sequence $a_{i, j}$ of integers such that $a_{1, n}=n^{n}$ for $n \geq 1$ and $a_{i, j}=a_{i-1, j}+a_{i-1, j+1}$ for all $i, j \geq 1$. Find the last (decimal) digit of $a_{128,1}$.-/
theorem number_theory_609403 {a : ℕ → ℕ → ℕ} (ha₁ : ∀n ≥ 1, a 1 n = n^n) (ha₂ : ∀i ≥ 1, ∀ j ≥ 1, a i j = a (i - 1) j + a (i - 1) (j + 1)) : a 128 1 ≡ 4 [MOD 10] := by
  rw [Nat.ModEq]
  simp
  set b := λi j ↦ a i j % 10 with hb₁
  have hb₂ : ∀i ≥ 1, ∀ j ≥ 1, b i j = (b (i - 1) j + b (i - 1) (j + 1)) % 10 := by
    intro i hi j hj
    rw [hb₁]
    simp
    rw [ha₂ i hi j hj]
  have hb₃ : ∀n ≥ 1, b 1 n = [0,1,4,7,6,5,6,3,6,9,0,1,6,3,6,5,6,7,4,9].getD (n % 20) 0 := by
    rw [hb₁]
    simp
    intro n hn
    rw [ha₁ n hn]
    mod_cases n % 20 <;>
      rw [Nat.ModEq] at H <;>
      simp at H <;>
      rw [H] <;>
      simp
    · -- n ≡ 0 [MOD 20]
      apply pow_mod_10_eq_0_of_mod_10_eq_0
      all_goals omega
    · -- n ≡ 1 [MOD 20]
      apply pow_mod_10_eq_1_of_mod_10_eq_1
      all_goals omega
    · -- n ≡ 2 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 2 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 2) % 10 = 2 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 3 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 3 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 3) % 10 = 3 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · -- n ≡ 4 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 4 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 4) % 10 = 4 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 5 [MOD 20]
      apply pow_mod_10_eq_5_of_mod_10_eq_5
      all_goals omega
    · -- n ≡ 6 [MOD 20]
      apply pow_mod_10_eq_6_of_mod_10_eq_6
      all_goals omega
    · -- n ≡ 7 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 7 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 7) % 10 = 7 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · -- n ≡ 8 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 8 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 8) % 10 = 8 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 9 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 9 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 9) % 10 = 9 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · -- n ≡ 10 [MOD 20]
      apply pow_mod_10_eq_0_of_mod_10_eq_0
      all_goals omega
    · -- n ≡ 11 [MOD 20]
      apply pow_mod_10_eq_1_of_mod_10_eq_1
      all_goals omega
    · -- n ≡ 12 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 12 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 12) % 10 = 2 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 13 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 13 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 13) % 10 = 3 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · -- n ≡ 14 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 14 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 14) % 10 = 4 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 15 [MOD 20]
      apply pow_mod_10_eq_5_of_mod_10_eq_5
      all_goals omega
    · -- n ≡ 16 [MOD 20]
      apply pow_mod_10_eq_6_of_mod_10_eq_6
      all_goals omega
    · -- n ≡ 17 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 17 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 17) % 10 = 7 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · -- n ≡ 18 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 18 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 18) % 10 = 8 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
      by_cases hk : k = 0
      · rw [hk]
      rw [Nat.mul_mod, pow_mod_10_eq_6_of_mod_10_eq_6]
      all_goals omega
    · -- n ≡ 19 [MOD 20]
      obtain ⟨k, hn₃⟩ := show ∃k, n = 20 * k + 19 by
        use n / 20
        omega
      rw [hn₃, Nat.pow_mod, show (20 * k + 19) % 10 = 9 by omega]
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num

  have ha₃ : ∀i ≥ 1, ∀ j ≥ 1, a i j = (∑ k ∈ Finset.range i, (Nat.choose (i - 1) k * a 1 (j + k))) := by
    intro i hi₁
    induction' i using Nat.strongRec with i hi₂
    by_cases hi₃ : i = 1
    · rw [hi₃]
      simp
    intro j hj
    rw [ha₂, hi₂ (i - 1) (by omega)]
    have : a (i - 1) (j + 1) = ∑ s ∈ Finset.Icc 1 (i - 1), (i - 1 - 1).choose (s - 1) * a 1 (j + s) := by
      rw [hi₂ _ (by omega) (by omega), Finset.sum_bij (λ k _ ↦ k + 1)]
      · simp; omega
      · simp
      · simp
        intro b h h'
        use b - 1
        omega
      · simp
        intro b hb
        rw [show j + (b + 1) = j + 1 + b by omega]
        simp
      omega
    rw [this]
    have : ∑ k ∈ Finset.range (i - 1), (i - 1 - 1).choose k * a 1 (j + k) = a 1 j + ∑ k ∈ Finset.Icc 1 (i - 2), (i - 2).choose k * a 1 (j + k) := by
      have : Finset.range (i - 1) = insert 0 (Finset.Icc 1 (i - 2)) := by
        ext x; simp
        omega
      rw [this, show i - 1 - 1 = i - 2 by omega]
      simp
    rw [this]
    have : ∑ s ∈ Finset.Icc 1 (i - 1), (i - 1 - 1).choose (s - 1) * a 1 (j + s) = ∑ s ∈ Finset.Icc 1 (i - 2), (i - 2).choose (s - 1) * a 1 (j + s) + a 1 (j + i - 1) := by
      have : Finset.Icc 1 (i - 1) = insert (i - 1) (Finset.Icc 1 (i - 2)) := by
        ext x; simp
        omega
      rw [this, Finset.sum_insert, show i - 1 - 1 = i - 2 by omega]
      simp
      rw [show j + (i - 1) = j + i - 1 by omega, add_comm]
      simp
      omega
    rw [this, ←add_assoc, add_assoc (a 1 j), ←Finset.sum_add_distrib]
    have : ∑ x ∈ Finset.Icc 1 (i - 2), ((i - 2).choose x * a 1 (j + x) + (i - 2).choose (x - 1) * a 1 (j + x)) = ∑ x ∈ Finset.Icc 1 (i - 2), (i - 1).choose x * a 1 (j + x) := by
      apply Finset.sum_congr (by rfl)
      simp
      intro x hx₁ hx₂
      rw [←add_mul, show i - 1 = (i - 2) + 1 by omega, ]
      simp
      apply Or.inl
      rw [Nat.choose_succ_left, add_comm]
      omega
    rw [this]
    have : Finset.range i = insert 0 (insert (i - 1) (Finset.Icc 1 (i - 2))) := by
      ext x; simp
      omega
    rw [this, Finset.sum_insert, Finset.sum_insert, show j + (i - 1) = j + i - 1 by omega]
    simp
    rw [add_assoc, add_comm (a 1 (j + i - 1))]
    simp; omega
    simp; omega
    all_goals omega
  rw [ha₃ _ (by linarith) _ (by linarith), Finset.sum_nat_mod]
  have : ∑ i ∈ Finset.range 128, (128 - 1).choose i * a 1 (1 + i) % 10 =  ∑ x ∈ Finset.range 128, Nat.choose 127 x * ([0,1,4,7,6,5,6,3,6,9,0,1,6,3,6,5,6,7,4,9].getD ((1 + x) % 20) 0) % 10 := by
    rw [Finset.sum_congr]
    simp
    simp
    intro x hx
    suffices a 1 (1 + x) % 10 = b 1 (1 + x) by
      rw [Nat.mul_mod, this, hb₃]
      simp
      omega
    rw [hb₁]
  rw [this]
  native_decide
