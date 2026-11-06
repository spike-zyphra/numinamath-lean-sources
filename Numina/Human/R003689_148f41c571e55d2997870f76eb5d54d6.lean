import Mathlib

set_option maxHeartbeats 1000000

lemma factorization_unique_2_3_11_19_53_61 {a b c d e f g h i j k l : ℕ} : 2^a * 3^b * 11^c * 19^d * 53^e * 61^f = 2^g * 3^h * 11^i * 19^j * 53^k * 61^l → a = g ∧ b = h ∧ c = i ∧ d = j ∧ e = k ∧ f = l := by
  intro h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  . apply congrArg (fun x => x.factorization 2) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h1
    rw [show (Nat.factorization 3) 2 = 0 by norm_num] at h1
    rw [show (Nat.factorization 11) 2 = 0 by norm_num] at h1
    rw [show (Nat.factorization 19) 2 = 0 by norm_num] at h1
    rw [show (Nat.factorization 53) 2 = 0 by norm_num] at h1
    rw [show (Nat.factorization 61) 2 = 0 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 3) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 3 = 0 by norm_num] at h1
    rw [show (Nat.factorization 3) 3 = 1 by norm_num] at h1
    rw [show (Nat.factorization 11) 3 = 0 by norm_num] at h1
    rw [show (Nat.factorization 19) 3 = 0 by norm_num] at h1
    rw [show (Nat.factorization 53) 3 = 0 by norm_num] at h1
    rw [show (Nat.factorization 61) 3 = 0 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 11) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 11 = 0 by norm_num] at h1
    rw [show (Nat.factorization 3) 11 = 0 by norm_num] at h1
    rw [show (Nat.factorization 11) 11 = 1 by norm_num] at h1
    rw [show (Nat.factorization 19) 11 = 0 by norm_num] at h1
    rw [show (Nat.factorization 53) 11 = 0 by norm_num] at h1
    rw [show (Nat.factorization 61) 11 = 0 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 19) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 19 = 0 by norm_num] at h1
    rw [show (Nat.factorization 3) 19 = 0 by norm_num] at h1
    rw [show (Nat.factorization 11) 19 = 0 by norm_num] at h1
    rw [show (Nat.factorization 19) 19 = 1 by norm_num] at h1
    rw [show (Nat.factorization 53) 19 = 0 by norm_num] at h1
    rw [show (Nat.factorization 61) 19 = 0 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 53) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 53 = 0 by norm_num] at h1
    rw [show (Nat.factorization 3) 53 = 0 by norm_num] at h1
    rw [show (Nat.factorization 11) 53 = 0 by norm_num] at h1
    rw [show (Nat.factorization 19) 53 = 0 by norm_num] at h1
    rw [show (Nat.factorization 53) 53 = 1 by norm_num] at h1
    rw [show (Nat.factorization 61) 53 = 0 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 61) at h1
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h1
    repeat rw [Nat.factorization_pow] at h1
    simp at h1
    rw [show (Nat.factorization 2) 61 = 0 by norm_num] at h1
    rw [show (Nat.factorization 3) 61 = 0 by norm_num] at h1
    rw [show (Nat.factorization 11) 61 = 0 by norm_num] at h1
    rw [show (Nat.factorization 19) 61 = 0 by norm_num] at h1
    rw [show (Nat.factorization 53) 61 = 0 by norm_num] at h1
    rw [show (Nat.factorization 61) 61 = 1 by norm_num] at h1
    simp at h1
    exact h1
    all_goals by_contra h; simp at h


lemma factorization_subset_primeFactors {n : ℕ} {F : Finset ℕ} (hn : n > 0) (hnF : n.primeFactors ⊆ F) (hF : ∀ p ∈ F, p.Prime): ∏ p ∈ F, p ^ n.factorization p = n := by
  nth_rw 2 [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  symm
  apply Finset.prod_subset hnF
  intro p hp1 hp2
  suffices n.factorization p = 0 by rw [this]; norm_num
  apply Nat.factorization_eq_zero_of_not_dvd
  contrapose hp2
  simp at hp2 ⊢
  exact ⟨hF p hp1, hp2, by omega⟩

lemma factorization_subset_primeFactors_2_3_11_19_53_61 {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 3, 11, 19, 53, 61} → 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 11 ^ n.factorization 11 * 19 ^ n.factorization 19 * 53 ^ n.factorization 53 * 61 ^ n.factorization 61 = n := by
  intro h
  have hp : ∀ p ∈ ({2, 3, 11, 19, 53, 61}: Finset ℕ), Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  have := factorization_subset_primeFactors hn h hp
  repeat rw [Finset.prod_insert (by norm_num)] at this
  rw [Finset.prod_singleton] at this
  linarith
  
theorem number_theory_207587 :
    {(a, b, c) : ℕ × ℕ × ℕ | 2 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ a * b * c = 2013 * 2014}.encard = 90 := by

  let S := {(a, b, c) : ℕ × ℕ × ℕ | 2 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ a * b * c = 2013 * 2014}
  let Tf := Finset.filter (fun ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6⟩ =>
    let a := 2^a1*3^a2*11^a3*19^a4*53^a5*61^a6;
    let b := 2^b1*3^b2*11^b3*19^b4*53^b5*61^b6;
    let c := 2^c1*3^c2*11^c3*19^c4*53^c5*61^c6;
    ( a1 + b1 + c1 = 1
    ∧ a2 + b2 + c2 = 1
    ∧ a3 + b3 + c3 = 1
    ∧ a4 + b4 + c4 = 1
    ∧ a5 + b5 + c5 = 1
    ∧ a6 + b6 + c6 = 1
    ∧ 2 ≤ a
    ∧ a ≤ b
    ∧ b ≤ c
    ∧ a * b * c = 2013 * 2014))
    ({0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1} ×ˢ {0, 1})


  let T := {(a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
    let a := 2^a1*3^a2*11^a3*19^a4*53^a5*61^a6;
    let b := 2^b1*3^b2*11^b3*19^b4*53^b5*61^b6;
    let c := 2^c1*3^c2*11^c3*19^c4*53^c5*61^c6;
    a1 + b1 + c1 = 1
    ∧ a2 + b2 + c2 = 1
    ∧ a3 + b3 + c3 = 1
    ∧ a4 + b4 + c4 = 1
    ∧ a5 + b5 + c5 = 1
    ∧ a6 + b6 + c6 = 1
    ∧ 2 ≤ a
    ∧ a ≤ b
    ∧ b ≤ c
    ∧ a * b * c = 2013 * 2014
  }

  have h_T_eq_Tf: T = Tf := by
    unfold Tf T
    ext ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6⟩
    simp
    omega

  have h_Tf_card: Tf.card = 90 := by native_decide

  have h_T_card: T.encard = 90 := by
    rw [h_T_eq_Tf, Set.encard_coe_eq_coe_finsetCard, h_Tf_card]
    norm_cast

  let f1 : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) := fun (a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6) => (2^a1*3^a2*11^a3*19^a4*53^a5*61^a6, 2^b1*3^b2*11^b3*19^b4*53^b5*61^b6, 2^c1*3^c2*11^c3*19^c4*53^c5*61^c6)

  have hf1 : Set.InjOn f1 T := by
    unfold f1 T
    intro ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6⟩ hx ⟨a1', a2', a3', a4', a5', a6', b1', b2', b3', b4', b5', b6', c1', c2', c3', c4', c5', c6'⟩ hy hxy
    simp at hxy
    obtain ⟨hxy1, hxy2, hxy3⟩ := hxy
    apply factorization_unique_2_3_11_19_53_61 at hxy1
    apply factorization_unique_2_3_11_19_53_61 at hxy2
    apply factorization_unique_2_3_11_19_53_61 at hxy3
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hxy1
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hxy2
    obtain ⟨h1'', h2'', h3'', h4'', h5'', h6''⟩ := hxy3
    subst a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 c1 c2 c3 c4 c5 c6
    rfl

  have h1 : f1 '' T = S := by
    unfold f1 T S
    ext x
    simp
    constructor
    . rintro ⟨a1,a2,a3,a4,a5,a6,b1,b2,b3,b4,b5,b6,c1,c2,c3,c4,c5,c6,⟨h1, h2, h3,h4,h5,h6,h7,h8,h9,h10⟩ , h⟩
      rw [← h]
      simp
      rw [show 2 ^ a1 * 3 ^ a2 * 11 ^ a3 * 19 ^ a4 * 53 ^ a5 * 61 ^ a6 * (2 ^ b1 * 3 ^ b2 * 11 ^ b3 * 19 ^ b4 * 53 ^ b5 * 61 ^ b6) * (2 ^ c1 * 3 ^ c2 * 11 ^ c3 * 19 ^ c4 * 53 ^ c5 * 61 ^ c6) = 2 ^ (a1 + b1 + c1) * 3 ^ (a2 + b2 + c2) * 11 ^ (a3 + b3 + c3) * 19 ^ (a4 + b4 + c4) * 53 ^ (a5 + b5 + c5) * 61 ^ (a6 + b6 + c6) by ring]
      rw [h1, h2, h3, h4, h5, h6]
      refine ⟨?_, ?_, ?_, by norm_num⟩
      all_goals assumption

    . intro ⟨hx1, hx2, hx3, hx⟩
      have : x.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.2.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.2.2 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have : x.1 * x.2.1 ≠ 0 := by by_contra h; rw [h] at hx; norm_num at hx
      have h1eq : 2 ^ x.1.factorization 2 * 3 ^ x.1.factorization 3 * 11 ^ x.1.factorization 11 * 19 ^ x.1.factorization 19 * 53 ^ x.1.factorization 53 * 61 ^ x.1.factorization 61 = x.1 := by
        apply factorization_subset_primeFactors_2_3_11_19_53_61 (by omega)
        have : x.1 ∣ 4054182 := by use x.2.1 * x.2.2; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 4054182 = {2, 3, 11, 19, 53, 61} by native_decide] at this
        exact this

      have h2eq : 2 ^ x.2.1.factorization 2 * 3 ^ x.2.1.factorization 3 * 11 ^ x.2.1.factorization 11 * 19 ^ x.2.1.factorization 19 * 53 ^ x.2.1.factorization 53 * 61 ^ x.2.1.factorization 61 = x.2.1 := by
        apply factorization_subset_primeFactors_2_3_11_19_53_61 (by omega)
        have : x.2.1 ∣ 4054182 := by use x.1 * x.2.2; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 4054182 = {2, 3, 11, 19, 53, 61} by native_decide] at this
        exact this

      have h3eq : 2 ^ x.2.2.factorization 2 * 3 ^ x.2.2.factorization 3 * 11 ^ x.2.2.factorization 11 * 19 ^ x.2.2.factorization 19 * 53 ^ x.2.2.factorization 53 * 61 ^ x.2.2.factorization 61 = x.2.2 := by
        apply factorization_subset_primeFactors_2_3_11_19_53_61 (by omega)
        have : x.2.2 ∣ 4054182 := by use x.1 * x.2.1; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 4054182 = {2, 3, 11, 19, 53, 61} by native_decide] at this
        exact this

      use x.1.factorization 2
      use x.1.factorization 3
      use x.1.factorization 11
      use x.1.factorization 19
      use x.1.factorization 53
      use x.1.factorization 61
      use x.2.1.factorization 2
      use x.2.1.factorization 3
      use x.2.1.factorization 11
      use x.2.1.factorization 19
      use x.2.1.factorization 53
      use x.2.1.factorization 61
      use x.2.2.factorization 2
      use x.2.2.factorization 3
      use x.2.2.factorization 11
      use x.2.2.factorization 19
      use x.2.2.factorization 53
      use x.2.2.factorization 61
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      . apply congrArg (fun x => x.factorization 2) at hx
        rw [show (Nat.factorization 4054182) 2 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 3) at hx
        rw [show (Nat.factorization 4054182) 3 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 11) at hx
        rw [show (Nat.factorization 4054182) 11 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 19) at hx
        rw [show (Nat.factorization 4054182) 19 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 53) at hx
        rw [show (Nat.factorization 4054182) 53 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . apply congrArg (fun x => x.factorization 61) at hx
        rw [show (Nat.factorization 4054182) 61 = 1 by native_decide] at hx
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hx
        exact hx
        all_goals assumption
      . rw [h1eq]
        exact hx1
      . rw [h1eq, h2eq]
        assumption
      . rw [h1eq, h2eq, h3eq]
        constructor <;> assumption
      . rw [h1eq, h2eq, h3eq]

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h_T_card] at h3
  exact h3
