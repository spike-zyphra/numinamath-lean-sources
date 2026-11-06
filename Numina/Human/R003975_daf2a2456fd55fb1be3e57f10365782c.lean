import Mathlib

/- # Problem:
 14.28. In how many different ways can 1000000 be represented as a product of three natural numbers? Products that differ only in the order of the factors are considered the same.

## 14.5. Inequalities for binomial coefficients
14.28. О т в е т: 139. Пусть множители имеют вид $2^{a_{1}} 5^{b_{1}}, 1^{a_{2}} 5^{b_{2}}$ и $2^{a_{3}} 5^{b_{3}}$. Тогда $a_{1}+a_{2}+a_{3}=6$ и $b_{1}+b_{2}+b_{3}=6$. При этом числа $a_{i}$ и $b_{i}$ могут быть равны нулю. Если $a_{1}=k$, то для разложения $a_{2}+a_{3}=6-k$ получаем $7-k$ вариантов. Поэтому для раза $a_{1}+a_{2}+a_{3}=6$ получаем $7+6+5+4+3+2+1=28$ вариантов. Всего получаем $28^{2}=784$ способа.

Но мы пока не учли тождественность разложений, отличающихся лишь порядком множителей. Есть ровно одно разложение, не зависящее от порядка множителей, в котором все множители равны 100 . Те разложения, в которых есть два равных множителя, мы посчитали трижды. В каждый из равных множителей 2 может входить в степени $0,1,2$ или 3 , т.е. всего четырьмя различными способами; столькими же способами может входить 5. Всего получаем 16 разложений такого вида, но одно из них - рассмотренное выше разложение с тремя равными множителями. Остаётся 15 разложений, каждое из которых мы посчитали трижды. Количество разложений с попарно различными множителями равно $784-1-45=738$. Каждое из них мы посчитали 6 раз, поэтому среди них будет $738 / 6=123$ различных разложений. Всего получаем $1+15+123=139$ разложений. -/

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

lemma factorization_subset_primeFactors_2_5 {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 5} → 2 ^ n.factorization 2 * 5 ^ n.factorization 5 = n := by
  intro h
  have hp : ∀ p ∈ ({2, 5}: Finset ℕ), Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals norm_num
  have := factorization_subset_primeFactors hn h hp
  rw [Finset.prod_pair (by norm_num)] at this
  exact this


theorem number_theory_226268:
  {(x, y, z) : ℕ × ℕ × ℕ | x * y * z = 10 ^ 6 ∧ x ≤ y ∧ y ≤ z}.encard = 139 := by

  let S := {(x, y, z) : ℕ × ℕ × ℕ | x * y * z = 10 ^ 6 ∧ x ≤ y ∧ y ≤ z}
  let Tf := Finset.filter (fun ⟨a, b, c, a', b', c'⟩ =>
    (a + b + c = 6
    ∧ a' + b' + c' = 6
    ∧ 2^a*5^a' ≤ 2^b*5^b' ∧ 2^b*5^b' ≤ 2^c*5^c'))
    (Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6 ×ˢ Finset.Icc (0 : ℕ) 6)

  let T := {(a, b, c, a', b', c') : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ | a + b + c = 6
    ∧ a' + b' + c' = 6
    ∧ 2^a*5^a' ≤ 2^b*5^b' ∧ 2^b*5^b' ≤ 2^c*5^c'
  }
  have h_T_eq_Tf: T = Tf := by
    unfold Tf T
    ext ⟨a, b, c, a', b', c'⟩
    simp
    omega

  have h_Tf_card: Tf.card = 139 := by native_decide

  have h_T_card: T.encard = 139 := by
    rw [h_T_eq_Tf, Set.encard_coe_eq_coe_finsetCard, h_Tf_card]
    norm_cast

  let f1 : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) := fun (a, b, c, a', b', c') => (2^a * 5^a', 2^b * 5^b', 2^c * 5^c')

  have hf1 : Set.InjOn f1 T := by
    unfold f1 T
    intro ⟨a, b, c, a', b', c'⟩ ⟨hx1, hx2, hx3, hx4⟩ ⟨a1, b1, c1, a2, b2, c2⟩ ⟨hy1, hy2, hy3, hy4⟩ hxy
    simp at hxy
    obtain ⟨hxy1, hxy2, hxy3⟩ := hxy
    apply factorization_unique at hxy1
    apply factorization_unique at hxy2
    apply factorization_unique at hxy3
    obtain ⟨h1, h2⟩ := hxy1
    obtain ⟨h3, h4⟩ := hxy2
    obtain ⟨h5, h6⟩ := hxy3
    subst a b c a' b' c'
    rfl

  have h1 : f1 '' T = S := by
    unfold f1 T S
    ext x
    simp
    constructor
    . rintro ⟨a, b, c, a', b', c', ⟨h1, h2, h3, h4⟩, h5⟩
      rw [← h5]
      simp
      rw [show 2 ^ a * 5 ^ a' * (2 ^ b * 5 ^ b') * (2 ^ c * 5 ^ c') = 2 ^ (a + b + c) * 5 ^ (a' + b' + c') by ring]
      rw [h1, h2]
      refine ⟨?_, ?_, ?_⟩
      . norm_num
      . assumption
      . assumption

    . intro ⟨hx, hx1, hx2⟩
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

      have h1eq : 2 ^ x.1.factorization 2 * 5 ^ x.1.factorization 5 = x.1 := by
        apply factorization_subset_primeFactors_2_5 (by omega)
        have : x.1 ∣ 1000000 := by use x.2.1 * x.2.2; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
        exact this

      have h2eq : 2 ^ x.2.1.factorization 2 * 5 ^ x.2.1.factorization 5 = x.2.1 := by
        apply factorization_subset_primeFactors_2_5 (by omega)
        have : x.2.1 ∣ 1000000 := by use x.1 * x.2.2; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
        exact this

      have h3eq : 2 ^ x.2.2.factorization 2 * 5 ^ x.2.2.factorization 5 = x.2.2 := by
        apply factorization_subset_primeFactors_2_5 (by omega)
        have : x.2.2 ∣ 1000000 := by use x.1 * x.2.1; rw [← hx]; ring
        have := Nat.primeFactors_mono this (by norm_num)
        rw [show Nat.primeFactors 1000000 = {2, 5} by native_decide] at this
        exact this

      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
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
      . rw [h1eq, h2eq]
        exact hx1
      . rw [h2eq, h3eq]
        exact hx2
      . apply Prod.ext
        . simp; exact h1eq
        . apply Prod.ext
          . simp; exact h2eq
          . simp; exact h3eq

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h_T_card] at h3
  exact h3
