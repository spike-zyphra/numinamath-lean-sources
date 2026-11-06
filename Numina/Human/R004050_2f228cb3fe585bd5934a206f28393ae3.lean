import Mathlib

/- # Problem:
 1. Let each of the numbers $x_{1}, x_{2}, \ldots, x_{n}$ be equal to 1 or -1 and also satisfy:

$$
x_{1} x_{2} x_{3} x_{4} + x_{2} x_{3} x_{4} x_{5} + \ldots + x_{n-2} x_{n-1} x_{n} x_{1} + x_{n-1} x_{n} x_{1} x_{2} + x_{n} x_{1} x_{2} x_{3} = 0
$$

Prove that $n$ is divisible by 4.
Решение. Нека

$$ \begin{aligned} & y_{k}=x_{k} x_{k+1} x_{k+2} x_{k+3}, \text {, а } k=1,2, \ldots, n-3, \\ & y_{n-2}=x_{n-2} x_{n-1} x_{n} x_{1}, y_{n-1}=x_{n-1} x_{n} x_{1} x_{2}, y_{n}=x_{n} x_{1} x_{2} x_{3} . \end{aligned} $$

Сите $y_{k}$ се 1 или -1 . Тогаш од условот на задачата добиваме

$$ y_{1}+\ldots+y_{n}=0 $$

Затоа мора да е $n=2 k$ и уште повеќе мора точно $k$ од броевите $y_{1}, \ldots, y_{n}$ да се еднакви на 1 и останатите $k$ да се еднакви на -1 . Но тогаш

$$ y_{1} \ldots y_{n}=(-1)^{k} $$

Од друга страна важи

$$ y_{1} y_{2} \ldots y_{n}=x_{1}^{4} x_{2}^{4} \ldots x_{n}^{4} $$

од каде добиваме $y_{1} y_{1} \ldots y_{n}=1$, па затоа $k=2 t$, односно имаме $n=4 t$. -/
theorem number_theory_233600 (n : ℕ) (hn : n > 0) (x : ℕ → ℤ)
  (hn1 : x (n + 1) = x 1) (hn2 : x (n + 2) = x 2) (hn3 : x (n + 3) = x 3)
  (hx : ∀ i, x i = 1 ∨ x i = -1) (hsum : ∑ i ∈ Finset.Icc 1 n, x i * x (i + 1) * x (i + 2) * x (i + 3) = 0) :
  4 ∣ n := by


  have h1 : ∀ i, x i * x (i + 1) * x (i + 2) * x (i + 3) = 1 ∨ x i * x (i + 1) * x (i + 2) * x (i + 3) = -1 := by
    intro i
    have h1:= hx i
    have h2:= hx (i + 1)
    have h3:= hx (i + 2)
    have h4:= hx (i + 3)
    rcases h1 with h1 | h1
    all_goals rcases h2 with h2 | h2
    all_goals rcases h3 with h3 | h3
    all_goals rcases h4 with h4 | h4
    all_goals rw [h1, h2, h3, h4]; simp


  let s1 := Finset.filter (fun i => x i * x (i + 1) * x (i + 2) * x (i + 3) = 1) (Finset.Icc 1 n)
  let s2 := Finset.filter (fun i => x i * x (i + 1) * x (i + 2) * x (i + 3) = -1) (Finset.Icc 1 n)

  have h_union : Finset.Icc 1 n = s1 ∪ s2 := by
    ext i
    unfold s1 s2
    simp
    have := h1 i
    omega

  have h_disj : Disjoint s1 s2 := by
    rw [disjoint_iff]
    unfold s1 s2
    ext i
    simp
    intro hi1 hi2 hx _ _
    rw [hx]
    simp

  have h_n_eq : n = s1.card + s2.card := by
    rw [show n = (Finset.Icc 1 n).card by simp]
    rw [h_union]
    rw [Finset.card_union]
    rw [show s1 ∩ s2 = ∅ by rw [disjoint_iff] at h_disj; exact h_disj]
    simp

  rw [h_union] at hsum
  rw [Finset.sum_union h_disj] at hsum
  have h_s1_sum : ∑ i ∈ s1, x i * x (i + 1) * x (i + 2) * x (i + 3) = ∑ i ∈ s1, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hi.2

  have h_s2_sum : ∑ i ∈ s2, x i * x (i + 1) * x (i + 2) * x (i + 3) = ∑ i ∈ s2, (-1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hi.2

  rw [h_s1_sum, h_s2_sum] at hsum
  simp at hsum
  have h_card_eq : s1.card = s2.card := by
    linarith

  have : Even n := by
    use s1.card
    nth_rw 2 [h_card_eq]
    exact h_n_eq

  obtain ⟨k, hk⟩ := this
  suffices Even k by
    rw [hk]
    obtain ⟨t, ht⟩ := this
    rw [ht]
    omega

  have h_prod_1_eq : ∏ i ∈ Finset.Icc 1 n, x (i + 1) = ∏ i ∈ Finset.Icc 1 n, x i := by
    nth_rw 1 [show n = n - 1 + 1 by omega]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [show n - 1 + 1 + 1 = n + 1 by omega]
    rw [hn1]
    have : ∏ i ∈ Finset.Icc 1 (n-1), x (i + 1) =  ∏ i ∈ Finset.Icc 2 n, x i := by
      have h1 : ∏ i ∈ Finset.Icc 1 (n - 1), x (i + 1) = ∏ i ∈ Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)), x i := by
        rw [Finset.prod_image]
        · -- Show that the function is injective
          intro i hi j hj h
          simp at h
          exact h
      have h2 : Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)) = Finset.Icc 2 n := by
        ext k
        simp
        omega
      rw [h1]
      simp
      rw [show n - 1 + 1 = n by omega]


    rw [this]
    nth_rw 2 [← Finset.mul_prod_Ioc_eq_prod_Icc (by omega)]
    rw [show Finset.Ioc 1 n = Finset.Icc 2 n by
      ext x
      simp
      omega
    ]
    ring

  have h_prod_2_eq : ∏ i ∈ Finset.Icc 1 n, x (i + 2) = ∏ i ∈ Finset.Icc 1 n, x i := by
    rw [← h_prod_1_eq]
    nth_rw 1 [show n = n - 1 + 1 by omega]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [show n - 1 + 1 + 2 = n + 2 by omega]
    rw [hn2]
    have : ∏ i ∈ Finset.Icc 1 (n-1), x (i + 2) =  ∏ i ∈ Finset.Icc 2 n, x (i + 1) := by
      have h1 : ∏ i ∈ Finset.Icc 1 (n - 1), x (i + 2) = ∏ i ∈ Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)), x (i + 1) := by
        rw [Finset.prod_image]
        · -- Show that the function is injective
          intro i hi j hj h
          simp at h
          exact h
      have h2 : Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)) = Finset.Icc 2 n := by
        ext k
        simp
        omega
      rw [h1]
      simp
      rw [show n - 1 + 1 = n by omega]
    rw [this]
    nth_rw 2 [← Finset.mul_prod_Ioc_eq_prod_Icc (by omega)]
    rw [show Finset.Ioc 1 n = Finset.Icc 2 n by
      ext x
      simp
      omega
    ]
    ring

  have h_prod_3_eq : ∏ i ∈ Finset.Icc 1 n, x (i + 3) = ∏ i ∈ Finset.Icc 1 n, x i := by
    rw [← h_prod_2_eq]
    nth_rw 1 [show n = n - 1 + 1 by omega]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [show n - 1 + 1 + 3 = n + 3 by omega]
    rw [hn3]
    have : ∏ i ∈ Finset.Icc 1 (n-1), x (i + 3) =  ∏ i ∈ Finset.Icc 2 n, x (i + 2) := by
      have h1 : ∏ i ∈ Finset.Icc 1 (n - 1), x (i + 3) = ∏ i ∈ Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)), x (i + 2) := by
        rw [Finset.prod_image]
        · -- Show that the function is injective
          intro i hi j hj h
          simp at h
          exact h
      have h2 : Finset.image (fun (j : ℕ) => j + 1) (Finset.Icc 1 (n - 1)) = Finset.Icc 2 n := by
        ext k
        simp
        omega
      rw [h1]
      simp
      rw [show n - 1 + 1 = n by omega]
    rw [this]
    nth_rw 2 [← Finset.mul_prod_Ioc_eq_prod_Icc (by omega)]
    rw [show Finset.Ioc 1 n = Finset.Icc 2 n by
      ext x
      simp
      omega
    ]
    ring

  have h_prod_n : ∏ i ∈ Finset.Icc 1 n, x i * x (i + 1) * x (i + 2) * x (i + 3) = 1 := by
    repeat rw [Finset.prod_mul_distrib]
    rw [h_prod_1_eq, h_prod_2_eq, h_prod_3_eq]
    ring_nf
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i hi
    have := hx i
    rcases this with h | h
    . rw [h]; simp
    . rw [h]; simp

  rw [h_union] at h_prod_n
  rw [Finset.prod_union h_disj] at h_prod_n
  have h_prod_s1 : ∏ i ∈ s1, x i * x (i + 1) * x (i + 2) * x (i + 3) = ∏ i ∈ s1, 1 := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hi.2

  have h_prod_s2 : ∏ i ∈ s2, x i * x (i + 1) * x (i + 2) * x (i + 3) = ∏ i ∈ s2, (-1) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hi.2

  rw [h_prod_s1, h_prod_s2] at h_prod_n
  simp at h_prod_n
  by_contra hc
  simp at hc
  have : k = s2.card := by omega
  rw [← this] at h_prod_n
  have : (-1) ^ k = -1 := Odd.neg_one_pow hc
  omega
