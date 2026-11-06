import Mathlib

open Real Finset

/- For $n \geq 2$, let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers such that  $$ \left(a_{1}+a_{2}+\cdots+a_{n}\right)\left(\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}\right) \leq\left(n+\frac{1}{2}\right)^{2} $$  Prove that $\max \left(a_{1}, \ldots, a_{n}\right) \leq 4 \min \left(a_{1}, \ldots, a_{n}\right)$. -/
theorem inequalities_604580 {n : ℕ} {M m : ℝ} (hn : n ≥ 2) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (h : (∑ i, a i) * (∑ i, 1 / a i) ≤ (n + 1 / 2) ^ 2) (hM : M = (univ.image a).max) (hm : m = (univ.image a).min) :
    M ≤ 4 * m := by

  -- Let $M$ be the maximum of $a_{1}, a_{2}, \ldots, a_{n}$
  -- let i₁ be the index of $M$
  have ⟨i₁, hi₁⟩ : ∃ i₁, a i₁ = M := by
    have : M ∈ univ.image a := by exact mem_of_max (id (Eq.symm hM))
    obtain ⟨i₁, h⟩ := mem_image.mp this
    use i₁, h.2

  -- assume that i₁ = 0, else we can swap the indices
  -- define a function swap that swaps two indices
  let swap (j k : Fin n) : Fin n → Fin n := λ i => if i = j then k else if i = k then j else i
  have hswap {i j k : Fin n} : swap j k (swap j k i) = i := by
    simp [swap]
    by_cases ha : i = j
    · simp [ha]
    · by_cases hb : i = k
      · simp [hb]
      · simp [ha, hb]
  -- show that the function swap is injective
  have himage {j k : Fin n} :  image (swap j k) univ = univ := by
    ext i
    simp [swap]
    use swap j k i
    apply hswap
  have hinj {j k : Fin n} : ∀ x ∈ univ, ∀ y ∈ univ, swap j k x = swap j k y → x = y := by
    intro x _ y _ heq
    rw [←@hswap (j := j) (k := k) x, ←@hswap (j := j) (k := k) y]
    simp [heq]
  -- given a, define a' as the function a after swapping the indices j and k
  let a' (a : Fin n → ℝ) (j k : Fin n) (i : Fin n) : ℝ := a (swap j k i)
  have ha' {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) {j k : Fin n} : ∀ i, 0 < a' a j k i := by
    intro i
    simp [a', swap]
    split_ifs
    all_goals (apply ha)
  -- the condition h is preserved after swapping the indices j and k
  have h' {a : Fin n → ℝ} (h : (∑ i, a i) * (∑ i, 1 / a i) ≤ (n + 1 / 2) ^ 2) {j k : Fin n} : (∑ i, a' a j k i) * (∑ i, 1 / a' a j k i) ≤ (n + 1 / 2) ^ 2 := by
    apply le_of_eq_of_le ?_ h
    simp [a']
    congr 1
    · rw [←Finset.sum_image hinj, himage]
    · rw [←Finset.sum_image (f := fun x => (a x)⁻¹) hinj, himage]
  -- the image of a is the same as the image of a' after swapping the indices j and k
  have haimage {a : Fin n → ℝ} {j k : Fin n} : image (a' a j k) univ = image a univ := by
    simp [a']
    ext i
    constructor <;> intro h
    · obtain ⟨a, ha⟩ := mem_image.mp h
      apply mem_image.mpr
      use swap j k a
      simp [hswap, ha.2]
    · obtain ⟨a, ha⟩ := mem_image.mp h
      apply mem_image.mpr
      use swap j k a
      simp [hswap, ha.2]

  let fin0 : Fin n := ⟨0, by exact Nat.zero_lt_of_lt hn⟩
  wlog h₁ : i₁ = fin0 generalizing a i₁ with H
  · -- if i₁ ≠ 0, swap the indices
    let a'' (i : Fin n) : ℝ := a' a fin0 i₁ i
    have hM' : M = (univ.image a'').max := by simp [hM, haimage]
    have hm' : m = (univ.image a'').min := by simp [hm, haimage]
    apply H a'' (ha' ha) (h' h) hM' hm' fin0
    · simp [a'', a', swap, hi₁]
    · simp
  · -- if i₁ = 0, then assume m is the minimum of a₁, a₂, ..., aₙ
    -- let i₂ be the index of m
    rw [h₁] at hi₁
    have ⟨i₂, hi₂⟩ : ∃ i₂, a i₂ = m := by
      have : m ∈ univ.image a := by exact mem_of_min (id (Eq.symm hm))
      obtain ⟨i₂, h⟩ := mem_image.mp this
      use i₂, h.2

    let fin1 : Fin n := ⟨1, by exact hn⟩

    -- wlog we can assume that i₂ = 1
    wlog h₂ : i₂ = fin1 generalizing a i₂ with H
    · -- if i₂ ≠ 1, swap the indices
      by_cases h0 : fin0 = i₂
      · rw [h0] at hi₁
        rw [←hi₁, ←hi₂]
        linarith only [ha i₂]
      let a'' (i : Fin n) : ℝ := a' a fin1 i₂ i
      have hM' : M = (univ.image a'').max := by simp [hM, haimage]
      have hm' : m = (univ.image a'').min := by simp [hm, haimage]
      apply H a'' (ha' ha) (h' h) hM' hm' ?_ fin1
      · simp [a'', a', swap, hi₂]
      · simp
      · simp [a'', a', swap, h0, fin0, fin1, hi₁]
    · -- if i₂ = 1, By Cauchy-Schwarz, one obtains
      -- [ \begin{aligned} \left(n + \frac{1}{2}\right)^{2} & \geq \left(a_{2} + a_{1} + a_{3} + \cdots + a_{n}\right)\left(\frac{1}{a_{1}}
      --  + \frac{1}{a_{2}} + \frac{1}{a_{3}} + \cdots + \frac{1}{a_{n}}\right) \ & \geq \left(\sqrt{\frac{a_{2}}{a_{1}}}
      -- + \sqrt{\frac{a_{1}}{a_{2}}} + 1 + \cdots + 1\right)^{2} \ & \geq (\sqrt{1 / M} + \sqrt{M} + (n-2))^{2}. \end{aligned} ]
      rw [h₂] at hi₂
      have h : √ ((∑ i, a (swap fin0 fin1 i)) * (∑ i, 1 / a i)) ≤ n + 1 / 2 := by
        rw [←Real.sqrt_sq (show (n + 1 / 2 : ℝ) ≥ 0 by linarith)]
        apply sqrt_le_sqrt
        apply le_of_eq_of_le ?_ h
        simp [swap]
        left
        rw [←Finset.sum_image hinj, himage]
      have hcauchy : ∑ i, √ (a (swap fin0 fin1 i) * (1 / a i)) ≤ (n + 1 / 2):= by
        apply le_trans ?_ h
        rw [sqrt_mul, Finset.sum_congr rfl (by intro _ _; rw [sqrt_mul]; apply le_of_lt; apply ha)]
        apply Real.sum_sqrt_mul_sqrt_le (f := fun i => a (swap fin0 fin1 i)) (g := fun i => 1 / a i)
        · intro i
          exact le_of_lt (ha (swap fin0 fin1 i))
        · intro i; simp; exact le_of_lt (ha i)
        · apply Finset.sum_nonneg
          intro i _
          exact le_of_lt (ha (swap fin0 fin1 i))

      -- assume that k = √ (M/ m), simplify the result
      let k := √ (M / m)
      have hMpos : M > 0 := by simp [←hi₁]; exact ha fin0
      have hmpos : m > 0 := by simp [←hi₂]; exact ha fin1
      have hMnonneg : M ≥ 0 := by exact le_of_lt hMpos
      have hmnonneg : m ≥ 0 := by exact le_of_lt hmpos
      have hMne : M ≠ 0 := by exact ne_of_gt hMpos
      have hmne : m ≠ 0 := by exact ne_of_gt hmpos
      have hkpos : k > 0 := by simp [k]; apply div_pos hMpos hmpos
      have hk : k ≠ 0 := by exact ne_of_gt hkpos
      have hknoneg : k ≥ 0 := by exact le_of_lt hkpos
      have ha (i : Fin n) : √ (a (swap fin0 fin1 i) * (1 / a i)) = if i = fin0 then 1 / k else if i = fin1 then k else 1 := by
        simp [swap, k]
        by_cases hi : i = fin1
        · simp [hi, fin1, fin0, hi₁, hi₂]
          ring_nf
        · by_cases hi' : i = fin0
          · simp [hi', fin1, fin0, hi₁, hi₂]
            field_simp
          · simp [hi, hi']
            rw [mul_inv_cancel₀]
            apply ne_of_gt
            exact ha i
      rw [Finset.sum_congr rfl (by intro _ _; rw [ha]), Finset.sum_ite, Finset.sum_ite] at hcauchy
      simp
      have h1 : filter (fun x ↦ x = fin0) univ = {fin0} := by ext i; simp
      have h2 : filter (fun x ↦ x = fin1) (filter (fun x ↦ ¬x = fin0) univ) = {fin1} := by ext i; simp [fin1, fin0]; intro h; simp [h]
      have h3 : filter (fun x ↦ ¬x = fin1) (filter (fun x ↦ ¬x = fin0) univ) = (univ.erase fin1).erase fin0 := by ext i; simp
      simp [h1, h2, h3] at hcauchy
      rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite] at hcauchy
      simp [fin0, fin1] at hcauchy
      simp [Nat.cast_sub (by exact Nat.le_sub_one_of_lt hn), Nat.cast_sub (by exact Nat.one_le_of_lt hn)] at hcauchy
      -- we have that (k - 2) * (2 * k - 1) ≤ 0
      have hmul : (k - 2) * (2 * k - 1) ≤ 0 := by
        calc
          _ = 2 * (k⁻¹ + (k + (↑n - ↑1 - ↑1)) - (n + 2⁻¹)) * k := by ring_nf; rw [mul_inv_cancel₀ hk]; ring
          _ ≤ 2 * ((n + 2⁻¹) - (n + 2⁻¹)) * k := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left
              · simp
                exact hcauchy
              · norm_num
            · simp
            · exact hknoneg
            · simp
          _ = 0 := by ring
      -- therefore, k ≤ 2
      -- and we have that M = k^2 * m ≤ 4m
      suffices h : k ≤ 2
      · simp [k] at h
        calc
          M = (√ (M / m)) ^ 2 * m := by rw [sq_sqrt]; field_simp; apply div_nonneg hMnonneg hmnonneg
          _ ≤ 2 ^ 2 * m := by rel [h]
          _ = 4 * m := by ring
      · by_contra h
        simp at h
        have : ¬ (k - 2) * (2 * k - 1) ≤ 0 := by nlinarith
        contradiction
