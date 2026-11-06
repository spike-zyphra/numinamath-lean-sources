import Mathlib

/-For how many integer values of $n$ between 1 and 474 inclusive does the decimal representation of $\frac{n}{475}$ terminate?-/
theorem number_theory_15570 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q} = 24 := by
  -- first show that n / 475 terminate is equivalent with 19 | n
  have AB_eq : {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q} = {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n} := by
    ext n
    simp
    intro _ _
    apply Iff.intro <;> intro h
    -- case1 : n / 475 = p / 10 ^ q => n = 19 * m
    . obtain ⟨p, q, hpq⟩ := h
      -- Exclude the denominator from the expression to n*10^q = 19*(25*p)
      have eq₁ : (n : ℝ) * 10 ^ q = 19 * (25 * p) := by
        calc
          n * 10 ^ q = 475 * ((n : ℝ) / 475) * 10 ^ q := by rw [mul_div_cancel₀]; norm_num
          _ = 475 * ((p / 10 ^ q) * 10 ^ q) := by rw [hpq]; ring_nf
          _ = 475 * p := by rw [div_mul_cancel₀]; positivity
          _ = 19 * (25 * p) := by ring_nf
      replace eq₁ : (n : ℤ) * 10 ^ q = 19 * (25 * p) := by norm_cast at eq₁ ⊢
      -- by equation above, we have n * 10 ^ q divided by 19
      have dvd₁ : 19 ∣ (n : ℤ) * 10 ^ q := by
        rw [eq₁]
        apply dvd_mul_right
      -- show that 19 and 10 ^ q is coprime
      have coprime₁ : IsCoprime (19 : ℤ) (10 ^ q) := by
        have coprime : IsCoprime 19 (10 : ℤ) := by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
        apply IsCoprime.pow_right
        exact coprime
      -- by the 19.coprime 10, we simply to 19 ∣ n
      apply IsCoprime.dvd_of_dvd_mul_right at dvd₁
      norm_cast at dvd₁
      exact coprime₁
    -- case2 : n = 19 * m => n / 475 = p / 10 ^ q
    . obtain ⟨m, hn⟩ := h
      use (4 * m)
      use (2)
      rw [hn]
      field_simp
      ring_nf
  -- construct a map φ from Finset.Icc 1 24 to {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n}
  let φ : {n : ℕ | 1 ≤ n ∧ n ≤ 24} → {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n} := fun n ↦ ⟨19 * n, ?_⟩
  pick_goal 2
  obtain ⟨n, hn1, hn2⟩ := n
  simp
  refine ⟨?_, ?_⟩
  repeat linarith only [hn1, hn2]
  -- show that φ is bijective
  have bijective₁ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    -- goal 1 : show φ is injective
    . intro m n eq₁
      obtain ⟨m, _, _⟩ := m
      obtain ⟨n, _, _⟩ := n
      simp [φ] at eq₁
      congr
    -- goal 2 : show φ is surjective
    . intro n 
      obtain ⟨n, hn1, hn2, hn3⟩ := n
      obtain ⟨m, hm⟩ := hn3
      -- show that m is in the domain of φ
      have hm1 : m ∈ {n : ℕ | 1 ≤ n ∧ n ≤ 24} := by
        simp
        rw [hm] at hn1 hn2
        refine ⟨?_, ?_⟩
        repeat linarith only [hn1, hn2]
      -- show that m = φ⁻¹ n
      use (⟨m, hm1⟩)
      simp [φ]
      linarith only [hm]
  -- calculate the ncard of C = {n : ℕ | 1 ≤ n ≤ 24}
  have C_ncard : {n : ℕ | 1 ≤ n ∧ n ≤ 24}.ncard = 24 := by
    calc
      {n : ℕ | 1 ≤ n ∧ n ≤ 24}.ncard = (Set.Icc 1 24).ncard := by congr
      _ = (Finset.Icc 1 24).card := by rw [<-Finset.coe_Icc, Set.ncard_coe_Finset]
      _ = 24 := by norm_num
  -- calculate the encard of C = {n : ℕ | 1 ≤ n ≤ 24}
  have C_encard : {n : ℕ | 1 ≤ n ∧ n ≤ 24}.encard = 24 := by
    rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, C_ncard] -- Set.ncard = Set.encard.toNat.
    norm_cast
    apply Set.finite_of_ncard_pos -- Show that the set B is finite.
    simp [C_ncard]
  -- by bijective and AB_eq, we get the encard of the desired set A
  have A_encard : {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q}.encard = 24 := by
    calc
      {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q}.encard = {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n}.encard := by rw [AB_eq]
      _ = {n : ℕ | 1 ≤ n ∧ n ≤ 24}.encard := by apply Set.encard_congr; apply Equiv.ofBijective at bijective₁; exact bijective₁.symm
      _ = 24 := by rw [C_encard]
  -- finally convert the encard to ncard, q.e.d
  rw [Set.Finite.encard_eq_coe, <-Set.ncard_def] at A_encard
  norm_cast at A_encard ⊢
  apply Set.finite_of_encard_eq_coe
  simp [A_encard]
  norm_cast
