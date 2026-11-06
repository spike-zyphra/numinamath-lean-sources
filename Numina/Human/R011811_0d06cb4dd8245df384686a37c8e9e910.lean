import Mathlib

open Finset

/- Let $n$ be a positive integer. Prove that at least $2^{n-1}+n$ numbers can be chosen from the set $\{1, 2, 3,\ldots ,2^n\}$ such that for any two different chosen numbers $x$ and $y$, $x+y$ is not a divisor of $x\cdot y$. -/
theorem number_theory_65295 (n : ℕ) (hn : 0 < n) :
    ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 (2 ^ n) ∧
      s.card ≥ 2 ^ (n - 1) + n ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬(x + y ∣ x * y) := by
  -- first constructor such s
  let f : ℕ → ℕ := fun k => 2 ^ (k + 1)
  let g : ℕ → ℕ := fun k => 2 * k + 1
  let s1 : Finset ℕ := Finset.image f (range n)
  let s2 : Finset ℕ := Finset.image g (range (2 ^ (n - 1)))
  let s : Finset ℕ := s1 ∪ s2
  use s
  have prime2 : Nat.Prime 2 := by norm_num
  constructor
  -- goal 1 : s ⊆ Icc 1 (2 ^ n) 
  · refine union_subset_iff.mpr ?_
    constructor
    refine image_subset_iff.mpr ?_
    intro x hx
    unfold f
    simp at hx
    simp
    constructor
    have xge : x ≥ 0 := by exact Nat.zero_le x
    exact Nat.one_le_two_pow
    have ineq : 2 ^ x < 2 ^ n := by 
      refine (Nat.pow_lt_pow_iff_right ?_).mpr hx
      linarith
    have xle : x + 1 ≤ n := by omega
    refine Nat.pow_le_pow_of_le_right ?_ hx
    linarith
    refine image_subset_iff.mpr ?_
    intro x hx
    simp at hx
    unfold g
    simp
    have ineq1 : 2 *  2 ^ (n - 1) = 2 ^ n := by 
      have aux : n = 1 + (n - 1) := by omega
      nth_rw 2 [aux]
      rw [pow_add]
      ring
    linarith
  constructor
  -- goal 2 : s.card ≥ 2 ^ (n - 1) + n
  · 
    have card1 : card s1 = n := by 
      unfold s1
      -- Finset.card_image_of_injective
      have aux : card (range n) = n := by 
        exact card_range n
      conv => 
        rhs
        rw [←aux]
      apply Finset.card_image_of_injective
      unfold f
      refine injective_of_le_imp_le (fun k => 2 ^ (k + 1)) ?_
      intro x y hxy
      simp at hxy
      have aux : x + 1 ≤ y + 1 := by 
        refine (Nat.pow_le_pow_iff_right ?_).mp hxy
        linarith
      linarith
    have card2 : card s2 = 2 ^ (n - 1) := by 
      unfold s2
      -- Finset.card_image_of_injective
      have aux : card (range (2 ^ (n - 1))) = (2 ^ (n - 1)) := by 
        exact card_range (2 ^ (n - 1))
      conv => 
        rhs
        rw [←aux]
      apply Finset.card_image_of_injective
      unfold g
      refine injective_of_le_imp_le (fun k => 2 * k + 1) ?_
      intro x y hxy
      simp at hxy
      exact hxy
    have card3 : card s = 2 ^ (n - 1) + n := by
      unfold s
      rw [←card2, ←card1, add_comm]
      apply card_union_of_disjoint
      refine disjoint_left.mpr ?_
      intro a ha
      unfold s1 at ha
      unfold s2
      simp at ha
      simp
      obtain ⟨b, hb1, hb2⟩ := ha
      unfold f at hb2
      intro c hc 
      unfold g
      have even_a : Even a := by 
        unfold Even
        use 2 ^ b
        rw [←hb2]
        rw [pow_add]
        ring
      have odd_c : Odd (2 * c + 1) := by 
        unfold Odd
        use c
      by_contra hc'
      rw [hc'] at odd_c
      obtain h2 := Nat.not_even_iff_odd.mpr odd_c
      exact h2 even_a
    rw [card3]
  -- goal 3 : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬(x + y ∣ x * y)
  intro x hx y hy hxy
  -- by cases x ∈ s1 ∧ y ∈ s1 ∨ x ∈ s1 ∧ y ∈ s2 ∨ x ∈ s2 ∧ y ∈ s1 ∨ x ∈ s2 ∧ y ∈ s2
  unfold s at hx
  unfold s at hy
  simp at hx hy
  obtain hx1 | hx2 := hx
  obtain hy1 | hy2 := hy
  -- the first case x ∈ s1 ∧ y ∈ s1
  unfold s1 at hx1 hy1
  simp at hx1 hy1
  obtain ⟨a, ha, haeq⟩ := hx1
  obtain ⟨b, hb, hbeq⟩ := hy1
  have aneqb : a ≠ b := by 
    by_contra hc
    rw [hc] at haeq
    rw [haeq] at hbeq
    exact hxy hbeq
  unfold f at haeq hbeq
  rw [←haeq, ←hbeq]
  -- since 2 ^ a + 2 ^ b has prime divisor other than two, then ¬ 2 ^ a + 2 ^ b ∣ 2 ^ a * 2 ^ b
  -- Nat.dvd_prime_pow
  rw [←pow_add]
  by_contra hc
  have prime2 : Nat.Prime 2 := by norm_num
  obtain ⟨k, kle, hk⟩ := (Nat.dvd_prime_pow prime2).mp hc
  by_cases altb : a < b 
  -- if a < b, then 2 ^ a + 2 ^ b = 2 ^ a * (1 + 2 ^ (b-a)), then we get 2 ^ (b-a) | k, which contradicts to the assumption.
  have powlt : 2 ^ (a + 1) < 2 ^ (b + 1) := by 
    refine (Nat.pow_lt_pow_iff_right ?_).mpr ?_
    linarith
    linarith
  have lt1 : 2 ^ k > 2 ^ (b + 1) := by 
    rw [←hk]
    have pos : 2 ^ (a + 1) > 0 := by positivity
    linarith
  have kgtb : k > b + 1 := by 
    refine (Nat.pow_lt_pow_iff_right ?_).mp lt1
    linarith
  have kltb : k < b + 2 := by 
    have aux : 2 ^ k < 2 ^ (b + 1 + 1) := by 
      rw [←hk]
      have aux2 : 2 ^ (b + 2) = 2 ^ (b + 1) + 2 ^ (b + 1) := by
        rw [pow_add]
        simp
        ring
      rw [aux2]

      linarith
    refine (Nat.pow_lt_pow_iff_right ?_).mp aux
    linarith
  linarith
  have blta : b < a := by omega
  -- if b < a, then 2 ^ b + 2 ^ a = 2 ^ b * (1 + 2 ^ (a-b)), then we get 2 ^ (a-b) | k, which contradicts to the assumption.
  have powlt : 2 ^ (a + 1) > 2 ^ (b + 1) := by 
    refine (Nat.pow_lt_pow_iff_right ?_).mpr ?_
    linarith
    linarith
  have lt1 : 2 ^ k > 2 ^ (a + 1) := by 
    rw [←hk]
    have pos : 2 ^ (b + 1) > 0 := by positivity
    linarith
  have kgtb : k > a + 1 := by 
    refine (Nat.pow_lt_pow_iff_right ?_).mp lt1
    linarith
  have kltb : k < a + 2 := by 
    have aux : 2 ^ k < 2 ^ (a + 1 + 1) := by 
      rw [←hk]
      have aux2 : 2 ^ (a + 1 + 1) = 2 ^ (a + 1) + 2 ^ (a + 1) := by
        rw [pow_add]
        simp
        ring
      rw [aux2]
      linarith
    refine (Nat.pow_lt_pow_iff_right ?_).mp aux
    linarith
  linarith
  -- the second case x ∈ s1 ∧ y ∈ s2
  unfold s1 at hx1
  unfold s2 at hy2
  simp at hx1 hy2
  obtain ⟨a, ha, haeq⟩ := hx1
  obtain ⟨c, hc, hceq⟩ := hy2
  unfold f at haeq
  unfold g at hceq
  rw [←haeq, ←hceq]
  by_contra h2
  have ndvd : ¬ 2 ^ (a + 1) + (2 * c + 1) ∣ 2 ^ (a + 1) := by
    by_contra h
    obtain ⟨k, kle, hk⟩ := (Nat.dvd_prime_pow prime2).mp h
    have even1 : Even (2 ^ (a + 1) + (2 * c + 1)) := by 
      rw [hk]
      refine (Nat.even_pow' ?_).mpr ?_
      by_contra hk0
      rw [hk0] at hk
      simp at hk
      have pos1 : 2 ^ (a + 1) > 0 := by positivity
      linarith
      norm_num
    have odd1 : Odd (2 ^ (a + 1) + (2 * c + 1)) := by 
      use (2 ^ a + c)
      rw [pow_add]
      ring
    obtain h1 := Nat.not_even_iff_odd.mpr odd1
    exact h1 even1
  have dvd1 : 2 ^ (a + 1) + (2 * c + 1) ∣ (2 * c + 1) := by 
    have coprime : Nat.Coprime (2 ^ (a + 1) + (2 * c + 1))  (2 ^ (a + 1)) := by
      refine (Nat.add_coprime_iff_right ?_).mpr ?_
      simp
      refine (Nat.Prime.coprime_pow_of_not_dvd prime2 ?_)
      omega
    exact Nat.Coprime.dvd_of_dvd_mul_left coprime h2
  have ge : 2 ^ (a + 1) + (2 * c + 1) ≤  2 * c + 1 := by 
    apply Nat.le_of_dvd
    linarith
    exact dvd1
  have pos : 2 ^ (a + 1)  > 0 := by positivity
  linarith
  obtain hy1 | hy2 := hy
  -- the third case x ∈ s2 ∧ y ∈ s1
  -- basically it is similar as the above case
  unfold s1 at hy1
  unfold s2 at hx2
  simp at hx2 hy1
  obtain ⟨a, ha, haeq⟩ := hy1
  obtain ⟨c, hc, hceq⟩ := hx2
  unfold f at haeq
  unfold g at hceq
  rw [←haeq, ←hceq]
  by_contra h2
  have ndvd : ¬ 2 ^ (a + 1) + (2 * c + 1) ∣ 2 ^ (a + 1) := by
    by_contra h
    obtain ⟨k, kle, hk⟩ := (Nat.dvd_prime_pow prime2).mp h
    have even1 : Even (2 ^ (a + 1) + (2 * c + 1)) := by 
      rw [hk]
      refine (Nat.even_pow' ?_).mpr ?_
      by_contra hk0
      rw [hk0] at hk
      simp at hk
      have pos1 : 2 ^ (a + 1) > 0 := by positivity
      linarith
      norm_num
    have odd1 : Odd (2 ^ (a + 1) + (2 * c + 1)) := by 
      use (2 ^ a + c)
      rw [pow_add]
      ring
    obtain h1 := Nat.not_even_iff_odd.mpr odd1
    exact h1 even1
  have dvd1 : (2 * c + 1) + 2 ^ (a + 1)∣ (2 * c + 1) := by 
    have coprime : Nat.Coprime ((2 * c + 1) + 2 ^ (a + 1))  (2 ^ (a + 1)) := by
      refine (Nat.add_coprime_iff_left ?_).mpr ?_
      simp
      refine (Nat.Prime.coprime_pow_of_not_dvd prime2 ?_)
      omega
    exact Nat.Coprime.dvd_of_dvd_mul_right coprime h2
  have ge :  (2 * c + 1) + 2 ^ (a + 1) ≤  2 * c + 1 := by 
    apply Nat.le_of_dvd
    linarith
    exact dvd1
  have pos : 2 ^ (a + 1)  > 0 := by positivity
  linarith
  -- the fourth case x ∈ s2 ∧ y ∈ s2
  -- basically it is by even number can not divides odd number 
  unfold s2 at hx2 hy2
  simp at hx2 hy2
  obtain ⟨a, ha, haeq⟩ := hx2
  obtain ⟨c, hc, hceq⟩ := hy2
  have aneqc : a ≠ c := by
    by_contra hc'
    unfold g at haeq hceq
    rw [hc', hceq] at haeq
    exact hxy (Eq.symm haeq)
  unfold g at haeq hceq
  rw [←haeq, ←hceq]
  have dvd2 : 2 ∣ 2 * a + 1 + (2 * c + 1) := by 
    use (a + c + 1)
    ring
  have ndvd : ¬ 2 ∣ (2 * a + 1) * (2 * c + 1) := by 
    have odd : Odd ((2 * a + 1) * (2 * c + 1)) := by 
      refine Nat.odd_mul.mpr ?_
      constructor 
      use a 
      use c
    exact Odd.not_two_dvd_nat odd
  by_contra h2
  obtain dvd3 := dvd_trans dvd2 h2
  exact ndvd dvd3