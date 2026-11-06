import Mathlib

/- How many natural number triples $(x,y,z)$ are there such that $xyz = 10^6$?

$
\textbf{(A)}\ 568
\qquad\textbf{(B)}\ 784
\qquad\textbf{(C)}\ 812
\qquad\textbf{(D)}\ 816
\qquad\textbf{(E)}\ 824
$ -/

lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl


lemma nat_triple_sum_6_encard :
  {(a, b, c) : ℕ × ℕ × ℕ | a + b + c = 6}.encard = 28 := by
  have : {(a, b, c) : ℕ × ℕ × ℕ | a + b + c = 6} = Finset.filter (fun s : ℕ × ℕ × ℕ => (s.1 + s.2.1 + s.2.2 = 6)) (Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6) := by
    ext ⟨a, b, c⟩
    simp
    omega
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  native_decide

lemma factorization_unique {a b c d : ℕ} : 2^a * 5^b = 2^c * 5^d → a = c ∧ b = d := by
  intro h
  constructor
  . apply congrArg (fun x => x.factorization 2) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h
    rw [show (Nat.factorization 5) 2 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 5) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 5 = 0 by norm_num] at h
    rw [show (Nat.factorization 5) 5 = 1 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h

lemma factorization_subset_primeFactors {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 5} → 2 ^ n.factorization 2 * 5 ^ n.factorization 5 = n := by
  intro h
  nth_rw 3 [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  have h_zero : ∀ p ∈ ({2, 5}: Finset ℕ), p ∉ n.primeFactors → p ^ n.factorization p = 1 := by
    intro p hp1 hp2
    suffices n.factorization p = 0 by
      rw [this]
      norm_num

    apply Nat.factorization_eq_zero_of_not_dvd
    contrapose hp2
    simp
    simp at hp2
    refine ⟨?_, hp2, by omega⟩
    simp at hp1
    rcases hp1 with rfl | rfl
    all_goals norm_num

  rw [Finset.prod_subset h h_zero]
  simp

theorem number_theory_36261 :
  {(x, y, z) : ℕ × ℕ × ℕ | x * y * z = 10 ^ 6}.encard = 784 := by

  let S := {(x, y, z) : ℕ × ℕ × ℕ | x * y * z = 10 ^ 6}
  let T := {(a, b, c) : ℕ × ℕ × ℕ | a + b + c = 6}
  let f1 : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) := fun ⟨(a, b, c), (d, e, f)⟩ => (2^a * 5^d, 2^b * 5^e, 2^c * 5^f)


  have hf1 : Set.InjOn f1 (T ×ˢ T) := by
    unfold Set.InjOn f1
    intro x hx y hy hxy
    simp at hx hy hxy
    obtain ⟨hxy1, hxy2, hxy3⟩ := hxy
    apply factorization_unique at hxy1
    apply factorization_unique at hxy2
    apply factorization_unique at hxy3
    have ⟨h1, h2⟩ := hxy1
    have ⟨h3, h4⟩ := hxy2
    have ⟨h5, h6⟩ := hxy3

    apply Prod.ext
    . apply Prod.ext
      . assumption
      . apply Prod.ext
        . assumption
        . assumption
    . apply Prod.ext
      . assumption
      . apply Prod.ext
        . assumption
        . assumption

  have h1 : f1 '' (T ×ˢ T) = S := by
    unfold f1 T Set.image S
    ext x
    simp
    constructor
    . rintro ⟨a, b, c, d, e, f, ⟨h1, h2⟩, h3⟩
      rw [← h3]
      simp
      rw [show 2 ^ a * 5 ^ d * (2 ^ b * 5 ^ e) * (2 ^ c * 5 ^ f) = 2 ^ (a + b + c) * 5 ^ (d + e + f) by ring]
      rw [h1, h2]
      norm_num

    . intro hx
      have : x.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.2.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.2.2 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.1 * x.2.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      use x.1.factorization 2
      use x.2.1.factorization 2
      use x.2.2.factorization 2
      use x.1.factorization 5
      use x.2.1.factorization 5
      use x.2.2.factorization 5
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . apply congrArg (fun x => x.factorization 2) at hx
        rw [show (Nat.factorization 1000000) 2 = 6 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 5) at hx
        rw [show (Nat.factorization 1000000) 5 = 6 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply Prod.ext
        . simp
          apply factorization_subset_primeFactors (by omega)
          have : x.1 ∣ 1000000 := by use x.2.1 * x.2.2; rw [← hx]; ring
          have := Nat.primeFactors_mono this (by norm_num)
          rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
          exact this
        . apply Prod.ext
          . simp
            apply factorization_subset_primeFactors (by omega)
            have : x.2.1 ∣ 1000000 := by use x.1 * x.2.2; rw [← hx]; ring
            have := Nat.primeFactors_mono this (by norm_num)
            rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
            exact this
          . simp
            apply factorization_subset_primeFactors (by omega)
            have : x.2.2 ∣ 1000000 := by use x.1 * x.2.1; rw [← hx]; ring
            have := Nat.primeFactors_mono this (by norm_num)
            rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
            exact this

  have h2 : (T ×ˢ T).encard = 784 := by
    have hT_encard : T.encard = 28 := nat_triple_sum_6_encard


    have hT_finite: T.encard < ⊤ := by
      rw [hT_encard]
      decide

    simp at hT_finite
    have : hT_finite.toFinset.card = 28 := by
      rw [Set.Finite.encard_eq_coe_toFinset_card hT_finite] at hT_encard
      norm_cast at hT_encard

    have h_TT_finite: (T ×ˢ T).Finite := Set.Finite.prod hT_finite hT_finite

    rw [Set.Finite.encard_eq_coe_toFinset_card h_TT_finite]
    norm_cast


    have h_eq : h_TT_finite.toFinset = hT_finite.toFinset ×ˢ hT_finite.toFinset := by
      rw [← Set.Finite.toFinset_prod]

    -- 使用积的基数公式
    rw [h_eq, Finset.card_product]
    rw [this]


  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h2] at h3
  exact h3
