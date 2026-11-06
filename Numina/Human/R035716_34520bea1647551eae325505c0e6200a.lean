import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Classical
open scoped BigOperators

/- Soit $n$ un entier naturel non nul. On dit qu'une fonction $f: \mathbb{R} \rightarrow \mathbb{R}$ est $n$-positive si, pour tous les réels $x_{1}, \ldots, x_{n}$ tels que $x_{1}+\ldots+x_{n}=0$, on a $f\left(x_{1}\right)+\ldots+f\left(x_{n}\right) \geqslant 0$.
a) Toute fonction 2020-positive est-elle nécessairement 1010-positive?
b) Toute fonction 1010-positive est-elle nécessairement 2020-positive? -/
theorem inequalities_606137
    (npos : (ℝ → ℝ) →  ℕ → Prop)
    (hnpos : npos = fun f n => n > 0 → ∀ x : Fin n → ℝ, (∑ i : Fin n, x i = 0) → (∑ i : Fin n, f (x i) ≥ 0)) :
    (∀ f, npos f 2020 → npos f 1010) ∧ ∃ f, ¬ (npos f 1010 → npos f 2020) := by

  -- show that if f is 2n-postive, then it is n-positive
  have hdiv {f : ℝ → ℝ} {n : ℕ} (h : npos f (2 * n)) : npos f n := by
    -- Let $f$ be a $2n$-positive function, and let $x_{1}, \ldots, x_{n}$ be real numbers such that $x_{1}+\ldots+x_{n}=0$.
    simp [hnpos] at h ⊢
    intro hn x hx
    let x' := fun i : Fin (2 * n) =>
      if h : i.val < n then x ⟨i.val, h⟩
      else x ⟨i.val - n, by refine Nat.sub_lt_left_of_lt_add ?H ?h; simp at h; exact h; apply lt_of_lt_of_eq i.2; ring⟩
    -- Noting that $x_{1}+\ldots+x_{n}+x_{1}+\ldots+x_{n}=0$
    have hx' {f : ℝ → ℝ} : ∑ i : Fin (2 * n), f (x' i) = 2 * (∑ i : Fin n, f (x i)) := by
      simp [x']
      let fin0 : Fin (2 * n) := ⟨0, by linarith⟩
      let finn : Fin (2 * n) := ⟨n, by linarith⟩
      let finl : Fin (2 * n) := ⟨2 * n - 1, by simp; exact hn⟩
      have hunion : univ (α := Fin (2 * n)) = Ico fin0 finn ∪ Icc finn finl := by
        ext ⟨i, hi⟩
        simp [fin0, finn, finl]
        by_cases h : i < n
        · simp [h]
        · simp [h]
          constructor
          · simp at h
            simp [h]
          · exact Nat.le_sub_one_of_lt hi
      rw [hunion, sum_union]
      · rw [show 2 * (∑ i : Fin n, f (x i)) = (∑ i : Fin n, f (x i)) + (∑ i : Fin n, f (x i)) by ring]
        congr 1
        · let g (i : Fin n) : Fin (2 * n) := ⟨i.val, by apply lt_trans i.2; exact lt_two_mul_self hn⟩
          have : Ico fin0 finn = image g univ := by
            ext ⟨i, hi⟩
            simp [fin0, finn, g]
            constructor <;> intro h
            · use ⟨i, h⟩
            · obtain ⟨a, ha⟩ := h
              simp [←ha]
          rw [this, sum_image]
          · simp [g]
          · intro x _ y _ hg
            simp [g] at hg
            exact Fin.eq_of_val_eq hg
        · let g (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by linarith [i.2]⟩
          have : Icc finn finl = image g univ := by
            ext ⟨i, hi⟩
            simp [finn, finl, g]
            constructor <;> intro h
            · use ⟨i - n, by rw [show 2 = 1 + 1 by simp, add_mul, one_mul] at hi; apply Nat.sub_lt_left_of_lt_add h.1 hi⟩
              simp
              rw [Nat.add_sub_cancel' h.1]
            · obtain ⟨a, ha⟩ := h
              simp [←ha]
              apply Nat.le_of_lt_succ
              calc
                _ < n + n := by rel [a.2]
                _ = _ := by
                  simp
                  rw [Nat.sub_add_cancel]
                  ring
                  exact Nat.one_le_of_lt hi
          rw [this, sum_image]
          · simp [g]
          · intro x _ y _ hg
            simp [g] at hg
            exact Fin.eq_of_val_eq hg
      · refine disjoint_left.mpr ?_
        intro ⟨a, ha⟩ ha'
        simp [fin0, finn, finl] at ha' ⊢
        simp [ha']
    have hsumx : ∑ i : Fin (2 * n), x' i = 0 := by
      rw [sum_congr rfl (fun i _ => show x' i = id (x' i) by simp)]
      rw [hx' (f := id)]
      simp [hx]
    -- we observe that
    -- $$ 0 \leqslant f\left(x_{1}\right)+\ldots+f\left(x_{n}\right)+f\left(x_{1}\right)+\ldots+f\left(x_{n}\right)=2\left(f\left(x_{1}\right)+\ldots+f\left(x_{n}\right)\right), $$0
    -- which shows that $f\left(x_{1}\right)+\ldots+f\left(x_{n}\right) \geqslant 0$, and thus that $f$ is $n$-positive.
    apply h hn x' at hsumx
    rw [hx'] at hsumx
    simp at hsumx
    exact hsumx


  constructor
  · intro f h
    apply hdiv h
  · --Let $f$ be the function defined by $f(x)=-1$ if $x$ is an integer such that $x \equiv 1(\bmod 2n)$, and by $f(x)=n$ otherwise.
    let f (x : ℝ) : ℝ := if ∃ k, k ≡ 1[ZMOD 2020] ∧ x = k then -1 else 1010
    use f
    simp [hnpos]
    constructor
    · --  Then $f$ is $n$-positive.
      --  let $x_{1}, \ldots, x_{n}$ be real numbers such that $x_{1}+\ldots+x_{n}=0$.
      intro x hx
      by_cases h : ∀ i, ∃ k, k ≡ 1[ZMOD 2020] ∧ x i = k
      · -- Otherwise, then $x_{k} \equiv 1(\bmod 2n)$ for all $k$
        let cast (i : Fin 1010) := (h i).choose
        have hcast {i : Fin 1010} : x i = 2020 * ↑((cast i - 1) / (2020 : ℤ) : ℤ) + 1 := by
          calc
            _ = ↑(cast i) := by simp [cast]; exact (h i).choose_spec.2
            _ = _ := by
              have : 1 ≡ cast i [ZMOD 2020] := by
                simp [cast]
                symm
                exact (h i).choose_spec.1
              apply Int.modEq_iff_dvd.mp at this
              obtain ⟨t, ht⟩ := this
              rw [ht]
              simp
              have : cast i = 2020 * t + 1 := by rw [←ht]; simp
              rw [this]
              simp
        -- so $x_{1}+\ldots+x_{n} \equiv n \not \equiv 0(\bmod 2n)$, which means that this case is actually impossible.
        have : ∃ t : ℤ, ∑ i : Fin 1010, x i = 2020 * t + 1010 := by
          use ↑(∑ i : Fin 1010, (cast i - 1) / (2020 : ℤ) : ℤ)
          simp [hcast]
          rw [sum_add_distrib, ←mul_sum, sum_const, card_univ, Fintype.card_fin]
          simp
        obtain ⟨t, ht⟩ := this
        rw [hx] at ht
        by_cases ht' : t = 0
        · simp [ht'] at ht
        · apply lt_or_gt_of_ne at ht'
          rcases ht' with ht' | ht'
          · have : (0 : ℝ) < 0 := by
              calc
                _ = 2020 * (t : ℝ) + 1010 := by simp [ht]
                _ ≤ 2020 * -1 + 1010 := by
                  apply add_le_add_right
                  apply mul_le_mul_of_nonneg_left
                  · rw [show (-1 : ℝ) = (-1 : ℤ) by simp]
                    apply Int.cast_le.mpr
                    linarith [ht']
                  · simp
                _ < 0 := by simp; norm_num
            simp at this
          · have : (0 : ℝ) > 0 := by
              calc
                _ = 2020 * (t : ℝ) + 1010 := by simp [ht]
                _ ≥ 2020 * 1 + 1010 := by
                  apply add_le_add_right
                  apply mul_le_mul_of_nonneg_left
                  · have : t ≥ 1 := by exact ht'
                    rw [show (1 : ℝ) = (1 : ℤ) by simp]
                    exact Int.cast_le.mpr ht'
                  · simp
                _ > 0 := by simp; norm_num
            simp at this
      · -- If there exists an integer $k$ such that $f\left(x_{k}\right)=n$,
        simp at h
        obtain ⟨i, hi⟩ := h
        have : f (x i) = 1010 := by
          simp only [f]
          rw [if_neg]
          simp
          exact hi
        -- and since $f\left(x_{i}\right) \geqslant-1$ for all $i \neq k$,
        -- we know that $f\left(x_{1}\right)+\ldots+f\left(x_{k}\right) \geqslant f\left(x_{k}\right)-(n-1) \geqslant 1$.
        have hge {i : ℝ} : f i ≥ -1 := by
          simp [f]
          split_ifs
          all_goals norm_num
        rw [show univ = {i} ∪ (univ.erase i) by rw [union_erase_of_mem]; simp; apply mem_singleton_self, sum_union]
        · simp only [sum_singleton]
          rw [this]
          calc
            (0 : ℝ) ≤ 1 := by norm_num
            _ = 1010 + ∑ x_1 ∈ univ.erase i, -1 := by rw [sum_erase_eq_sub, sum_const, card_univ, Fintype.card_fin]; ring; simp
            _ ≤ 1010 + ∑ x_1 ∈ univ.erase i, f (x x_1) := by
              apply add_le_add_left
              apply sum_le_sum
              intro i _
              exact hge
        · simp
    · --  However, $f$ is not $2n$-positive.
      --  if $x_{1}=1-2n$ and $x_{2}=x_{3}=\ldots=x_{2n}=1$
      let x : Fin 2020 → ℝ := fun i => if i = 0 then -2019 else 1
      use x
      constructor
      · --  then $x_{1}+\ldots+x_{2n}=0$
        simp [x]
        rw [sum_ite, sum_const, sum_const, filter_eq', filter_ne', card_erase_of_mem, card_univ, Fintype.card_fin]
        · simp
        · simp
      · --  but $f\left(x_{1}\right)+\ldots+f\left(x_{2n}\right)=-1-2019=-2020<0$.
        have {i : Fin 2020} : f (x i) = -1 := by
          simp only [f, x]
          by_cases hi : i = 0
          · simp only [if_pos hi]
            rw [if_pos]
            use -2019
            simp
            apply Int.modEq_iff_dvd.mpr
            use 1
            simp
          · simp only [if_neg hi]
            rw [if_pos]
            use 1
            simp
        rw [sum_congr rfl (fun i _ => this)]
        rw [sum_const, card_univ, Fintype.card_fin]
        simp
