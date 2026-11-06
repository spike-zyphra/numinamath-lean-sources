import Mathlib

open Finset

set_option maxHeartbeats 0

/- Let $a_{0}, a_{1}, a_{2}, \ldots$ be a sequence of real numbers such that $a_{0}=0, a_{1}=1$, and for every $n \geqslant 2$ there exists $1 \leqslant k \leqslant n$ satisfying  $$ a_{n}=\frac{a_{n-1}+\cdots+a_{n-k}}{k} $$  Find the maximal possible value of $a_{2018}-a_{2017}$.  (Belgium)-/
theorem algebra_23547 :
    IsGreatest {x : ℝ | ∃ a : ℕ → ℝ, a 0 = 0 ∧ a 1 = 1 ∧ (∀ n ≥ 2, ∃ k ∈ Icc 1 n, a n = (∑ i ∈ Icc 1 k, a (n - i)) / k) ∧ x = a 2018 - a 2017} (2016 / 2017 ^ 2) := by
  simp [IsGreatest]
  constructor
  · -- The claimed maximal value is achieved at $$ \begin{gathered} a_{1}=a_{2}=\cdots=a_{2016}=1, \quad a_{2017}=\frac{a_{2016}+\cdots+a_{0}}{2017}=1-\frac{1}{2017},
    -- \ a_{2018}=\frac{a_{2017}+\cdots+a_{1}}{2017}=1-\frac{1}{2017^{2}} . \end{gathered} $$
    let a (i : ℕ) : ℝ := if i = 0 then 0 else if i ≤ 2016 then 1 else if i = 2017 then 1 - 1 / 2017 else 1 - 1 / 2017 ^ 2
    use a
    simp [a]
    constructor
    · intro n hn
      have : ¬ n = 0 := by exact Nat.not_eq_zero_of_lt hn
      simp [this]
      by_cases hn' : n ≤ 2016
      · simp [hn']
        use 1
        simp
        constructor
        · exact Nat.one_le_of_lt hn
        · have : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hn
          simp [this]
          have : n ≤ 2017 := by exact Nat.le_succ_of_le hn'
          simp [this]
      · simp [hn']
        by_cases hn' : n = 2017
        · simp [hn']
          use 2017
          simp
          field_simp
          rw [sum_ite]
          simp
          have : filter (fun x ↦ ¬2017 - x = 0) (Icc 1 2017) = Icc 1 2016 := by
            ext x
            simp
            constructor
            · intro hx
              constructor
              · exact hx.1.1
              · apply Nat.le_of_lt_succ
                apply lt_of_le_of_ne hx.1.2
                obtain h := hx.2
                exact ne_of_apply_ne (HSub.hSub 2017) h
            · intro hx
              split_ands
              · exact hx.1
              · apply le_trans hx.2; simp
              · apply ne_of_gt
                simp
                exact Nat.lt_succ_of_le hx.2
          rw [this, sum_ite]
          have : filter (fun x ↦ ¬2017 ≤ 2016 + x) (Icc 1 2016) = ∅ := by
            ext x
            simp
            intro hx₁ _
            exact Nat.sub_le_iff_le_add'.mp hx₁
          rw [this, sum_empty]
          have : filter (fun x ↦ 2017 ≤ 2016 + x) (Icc 1 2016) = Icc 1 2016 := by
            ext x
            simp
            intro hx₁ _
            exact Nat.sub_le_iff_le_add'.mp hx₁
          rw [this, sum_const]
          norm_num
        · simp [hn']
          by_cases hn' : n = 2018
          · use 2017
            simp [hn']
            field_simp
            rw [sum_ite]
            simp
            have : filter (fun x ↦ ¬2018 - x = 0) (Icc 1 2017) = Icc 1 2017 := by
              ext x
              simp
              intro _ h
              apply ne_of_gt
              simp
              exact Nat.lt_add_one_of_le h
            rw [this, sum_ite]
            have : filter (fun x ↦ ¬2018 ≤ 2016 + x) (Icc 1 2017) = {1} := by
              ext x
              simp
              constructor <;> intro h
              · apply le_antisymm ?_ h.1.1
                linarith only [h.2]
              · simp [h]
            rw [this]
            have : filter (fun x ↦ 2018 ≤ 2016 + x) (Icc 1 2017) = Icc 2 2017 := by
              ext x
              simp
              constructor <;> intro h
              · constructor
                · linarith only [h.2]
                · exact h.1.2
              · split_ands
                · linarith only [h.1]
                · exact h.2
                · linarith only [h.1]
            rw [this]
            simp
            norm_num
          · use 1
            simp
            constructor
            · exact Nat.one_le_of_lt hn
            · have : ¬ n - 1 = 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hn
              simp [this]
              have : ¬ n ≤ 2017 := by
                rename_i h₁ h₂
                simp at h₁ ⊢
                exact Nat.lt_of_le_of_ne h₁ fun a ↦ h₂ (id (Eq.symm a))
              simp [this]
              simp [hn']
    · field_simp
      ring
  · -- Now we need to show that this value is optimal.
    intro r hr
    simp at hr
    obtain ⟨a, ha0, ha1, han, hr⟩ := hr
    rw [hr]
    -- For brevity, we use the notation $$ S(n, k)=a_{n-1}+a_{n-2}+\cdots+a_{n-k} \quad \text { for nonnegative integers } k \leqslant n \text {. } $$
    let S (n k : ℕ) : ℝ := ∑ i ∈ Icc 1 k, a (n - i)
    -- In particular, $S(n, 0)=0$ and $S(n, 1)=a_{n-1}$.
    have hSn0 {n : ℕ} : S n 0 = 0 := by simp [S]
    have hSn1 {n : ℕ} : S n 1 = a (n - 1) := by simp [S]
    -- In these terms, for every integer $n \geqslant 2$ there exists a positive integer $k \leqslant n$ such that $a_{n}=S(n, k) / k$.
    have han {n : ℕ} (hn : n ≥ 2) : ∃ k ∈ Icc 1 n, a n = S n k / k := by
      obtain ⟨k, hk, heq⟩ := han n hn
      use k
      simp [hk]
      rw [heq]
    -- For every integer $n \geqslant 1$ we define $$ M_{n}=\max _{1 \leqslant k \leqslant n} \frac{S(n, k)}{k}, \quad m_{n}=\min _{1 \leqslant k \leqslant n} \frac{S(n, k)}{k}, \quad \text { and } \quad \Delta_{n}=M_{n}-m_{n} \geqslant 0 .
    let M (n : ℕ) (hn : n ≥ 1) : ℝ := ((Icc 1 n).image (fun k => S n k / k)).max' (by simp [hn])
    let m (n : ℕ) (hn : n ≥ 1) : ℝ := ((Icc 1 n).image (fun k => S n k / k)).min' (by simp [hn])
    let Δ (n : ℕ) (hn : n ≥ 1) : ℝ := M n hn - m n hn
    -- $$ By definition, $a_{n} \in\left[m_{n}, M_{n}\right]$ for all $n \geqslant 2$;
    have ha_n_le {n : ℕ} (hn : n ≥ 2) : a n ≤ M n (by exact Nat.one_le_of_lt hn) := by
      apply le_max'
      apply mem_image.mpr
      obtain ⟨k, hk, heq⟩ := han hn
      use k, hk
      rw [heq]
    have ha_n_ge {n : ℕ} (hn : n ≥ 2) : m n (by exact Nat.one_le_of_lt hn) ≤ a n := by
      apply min'_le
      apply mem_image.mpr
      obtain ⟨k, hk, heq⟩ := han hn
      use k, hk
      rw [heq]
    -- on the other hand, $a_{n-1}=S(n, 1) / 1 \in\left[m_{n}, M_{n}\right]$.
    have ha_n_sub_one_le {n : ℕ} (hn : n ≥ 2) : a (n - 1) ≤ M n (by exact Nat.one_le_of_lt hn) := by
      apply le_max'
      simp
      use 1
      simp
      constructor
      · exact Nat.one_le_of_lt hn
      · simp [S]
    have ha_n_sub_one_ge {n : ℕ} (hn : n ≥ 2) : m n (by exact Nat.one_le_of_lt hn) ≤ a (n - 1) := by
      apply min'_le
      simp
      use 1
      simp
      constructor
      · exact Nat.one_le_of_lt hn
      · simp [S]

    -- Also by definition, for any $0< k \leqslant n$ we have $k m_{n} \leqslant S(n, k) \leqslant k M_{n}$; notice that these inequalities are also valid for $k=0$.
    -- Claim 1. For every $n>2$, we have $\Delta_{n} \leqslant \frac{n-1}{n} \Delta_{n-1}$.
    have hclaim (n : ℕ) (hn : n > 2) : Δ n (by exact Nat.one_le_of_lt hn) ≤ (n - 1) / n * Δ (n - 1) (by apply Nat.le_sub_of_add_le; simp; exact Nat.le_of_succ_le hn) := by
      -- Proof. Choose positive integers $k, \ell \leqslant n$ such that $M_{n}=S(n, k) / k$ and $m_{n}=S(n, \ell) / \ell$. 
      have hmax_mem : M n (by exact Nat.one_le_of_lt hn) ∈ (Icc 1 n).image (fun k => S n k / k) := by apply max'_mem
      simp at hmax_mem
      obtain ⟨k, ⟨hk₁, hk₂⟩, hM⟩ := hmax_mem
      have hmin_mem : m n (by exact Nat.one_le_of_lt hn) ∈ (Icc 1 n).image (fun k => S n k / k) := by apply min'_mem
      simp at hmin_mem
      obtain ⟨ℓ, ⟨hℓ₁, hℓ₂⟩, hm⟩ := hmin_mem
      -- We have $S(n, k)=a_{n-1}+S(n-1, k-1)$, so $$ k\left(M_{n}-a_{n-1}\right)=S(n, k)-k a_{n-1}=S(n-1, k-1)-(k-1) a_{n-1} \leqslant(k-1)\left(M_{n-1}-a_{n-1}\right), $$ since $S(n-1, k-1) \leqslant(k-1) M_{n-1}$.
      have h₁ : M n (by exact Nat.one_le_of_lt hn) - a (n - 1) ≤ (n - 1) / n * (M (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn) - a (n - 1)) := by
        have : k * (M n (by exact Nat.one_le_of_lt hn) - a (n - 1)) ≤ (k - 1) * (M (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn) - a (n - 1)) := by
          by_cases hk : k = 1
          · simp [←hM, hk, S]
          · trans S n k - k * a (n - 1)
            · apply le_of_eq
              rw [←hM]
              field_simp
            trans S (n - 1) (k - 1) - (k - 1) * a (n - 1)
            · apply le_of_eq
              simp [S]
              rw [Icc_eq_cons_Ioc hk₁, sum_cons]
              apply sub_eq_zero.mp
              ring_nf
              apply sub_eq_zero.mpr
              have : (Ioc 1 k).image (fun x => x - 1) = Icc 1 (k - 1) := by
                ext i
                simp
                constructor <;> intro h
                · obtain ⟨a, ⟨h₁, h₂⟩, hi⟩ := h
                  rw [←hi]
                  constructor
                  · exact Nat.le_sub_one_of_lt h₁
                  · exact Nat.sub_le_sub_right h₂ 1
                · use i + 1
                  split_ands
                  · apply Nat.lt_succ_of_le h.1
                  · apply Nat.add_le_of_le_sub hk₁ h.2
                  · simp
              rw [←this, sum_image]
              apply sum_congr rfl
              intro i hi
              simp at hi
              congr 1
              apply Nat.eq_sub_of_add_eq
              rw [←Nat.add_sub_assoc, Nat.sub_add_cancel]
              · apply le_trans hi.2 hk₂
              · apply le_of_lt hi.1
              intro x hx y hy h
              simp at hx hy
              apply tsub_left_inj (le_of_lt hx.1) (le_of_lt hy.1) |>.mp h
            · rw [mul_sub]
              gcongr
              rw [mul_comm]
              apply div_le_iff₀ ?_ |>.mp
              apply le_max'
              simp
              use k - 1
              split_ands
              · apply Nat.le_sub_of_add_le 
                apply Nat.succ_le_of_lt
                apply lt_of_le_of_ne hk₁
                exact fun a => hk (id (Eq.symm a))
              · gcongr
              · rw [Nat.cast_sub hk₁]
                simp
              · simp
                apply lt_of_le_of_ne hk₁
                exact fun a => hk (id (Eq.symm a))
        -- $$ Since $m_{n-1} \leqslant a_{n-1} \leqslant M_{n-1}$ and $k, \ell \leqslant n$, the obtained inequalities yield $$ \begin{array}{ll} M_{n}-a_{n-1} \leqslant \frac{k-1}{k}\left(M_{n-1}-a_{n-1}\right) \leqslant \frac{n-1}{n}\left(M_{n-1}-a_{n-1}\right)
        trans (k - 1) / k * (M (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn) - a (n - 1))
        · rw [mul_comm, ←mul_div_assoc]
          apply le_div_iff₀ ?_ |>.mpr
          rw [mul_comm]
          apply le_trans this
          apply le_of_eq
          ring
          positivity
        · apply mul_le_mul_of_nonneg_right
          · apply sub_nonneg.mp
            field_simp
            apply div_nonneg
            · ring_nf
              simp [hk₂]
            · positivity
          · simp
            apply le_trans (ha_n_le ?_) (by rfl)
            exact Nat.le_sub_one_of_lt hn
      --   Similarly, we get $$ \ell\left(a_{n-1}-m_{n}\right)=(\ell-1) a_{n-1}-S(n-1, \ell-1) \leqslant(\ell-1)\left(a_{n-1}-m_{n-1}\right) . $$ Since $m_{n-1} \leqslant a_{n-1} \leqslant M_{n-1}$ and $k, \ell \leqslant n$, the obtained inequalities yield $$ \begin{array}{ll} M_{n}-a_{n-1} \leqslant \frac{k-1}{k}\left(M_{n-1}-a_{n-1}\right) \leqslant \frac{n-1}{n}\left(M_{n-1}-a_{n-1}\right) \quad \text { and } \ a_{n-1}-m_{n} \leqslant \frac{\ell-1}{\ell}\left(a_{n-1}-m_{n-1}\right) \leqslant \frac{n-1}{n}\left(a_{n-1}-m_{n-1}\right) . \end{array} $$
      have h₂ : a (n - 1) - m n (by exact Nat.one_le_of_lt hn) ≤ (n - 1) / n * (a (n - 1) - m (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn)) := by
        have : ℓ * (a (n - 1) - m n (by exact Nat.one_le_of_lt hn)) ≤ (ℓ - 1) * (a (n - 1) - m (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn)) := by
          by_cases hℓ : ℓ = 1
          · simp [←hm, hℓ, S]
          · trans ℓ * a (n - 1) - S n ℓ
            · apply le_of_eq
              rw [←hm]
              field_simp
              ring
            trans (ℓ - 1) * a (n - 1) - S (n - 1) (ℓ - 1)
            · apply le_of_eq
              simp [S]
              rw [Icc_eq_cons_Ioc hℓ₁, sum_cons]
              apply sub_eq_zero.mp
              ring_nf
              rw [neg_add_eq_sub]
              apply sub_eq_zero.mpr
              have : (Ioc 1 ℓ).image (fun x => x - 1) = Icc 1 (ℓ - 1) := by
                ext i
                simp
                constructor <;> intro h
                · obtain ⟨a, ⟨h₁, h₂⟩, hi⟩ := h
                  rw [←hi]
                  constructor
                  · exact Nat.le_sub_one_of_lt h₁
                  · exact Nat.sub_le_sub_right h₂ 1
                · use i + 1
                  split_ands
                  · apply Nat.lt_succ_of_le h.1
                  · apply Nat.add_le_of_le_sub hℓ₁ h.2
                  · simp
              rw [←this, sum_image]
              apply sum_congr rfl
              intro i hi
              simp at hi
              congr 1
              symm
              apply Nat.eq_sub_of_add_eq
              rw [←Nat.add_sub_assoc, Nat.sub_add_cancel]
              · apply le_trans hi.2 hℓ₂
              · apply le_of_lt hi.1
              intro x hx y hy h
              simp at hx hy
              apply tsub_left_inj (le_of_lt hx.1) (le_of_lt hy.1) |>.mp h
            · rw [mul_sub]
              gcongr
              rw [mul_comm]
              apply le_div_iff₀ ?_ |>.mp
              apply min'_le
              simp
              use ℓ - 1
              split_ands
              · apply Nat.le_sub_of_add_le 
                apply Nat.succ_le_of_lt
                apply lt_of_le_of_ne hℓ₁
                exact fun a => hℓ (id (Eq.symm a))
              · gcongr
              · rw [Nat.cast_sub hℓ₁]
                simp
              · simp
                apply lt_of_le_of_ne hℓ₁
                exact fun a => hℓ (id (Eq.symm a))
        trans (ℓ - 1) / ℓ * (a (n - 1) - m (n - 1) (by apply Nat.le_sub_of_add_le; apply le_of_lt hn))
        · rw [mul_comm, ←mul_div_assoc]
          apply le_div_iff₀ ?_ |>.mpr
          rw [mul_comm]
          apply le_trans this
          apply le_of_eq
          ring
          positivity
        · apply mul_le_mul_of_nonneg_right
          · apply sub_nonneg.mp
            field_simp
            apply div_nonneg
            · ring_nf
              simp [hℓ₂]
            · positivity
          · simp
            apply le_trans (ha_n_ge ?_) (by rfl)
            exact Nat.le_sub_one_of_lt hn
      -- Therefore, $$ \Delta_{n}=\left(M_{n}-a_{n-1}\right)+\left(a_{n-1}-m_{n}\right) \leqslant \frac{n-1}{n}\left(\left(M_{n-1}-a_{n-1}\right)+\left(a_{n-1}-m_{n-1}\right)\right)=\frac{n-1}{n} \Delta_{n-1} . $$
      trans M n (by exact Nat.one_le_of_lt hn) - a (n - 1) + (a (n - 1) - m n (by exact Nat.one_le_of_lt hn))
      · apply le_of_eq
        ring
      · apply le_trans (add_le_add h₁ h₂)
        apply le_of_eq
        ring
    -- Back to the problem, if $a_{n}=1$ for all $n \leqslant 2017$, then $a_{2018} \leqslant 1$ and hence $a_{2018}-a_{2017} \leqslant 0$.
    let set_of_ne_one : Finset ℕ := (Icc 1 2017).filter (fun n => a n ≠ 1)
    by_cases hne : ¬ set_of_ne_one.Nonempty
    · simp [set_of_ne_one] at hne
      apply filter_eq_empty_iff.mp at hne
      simp at hne
      trans 1 - 1
      · gcongr
        · obtain ⟨k, hk, han⟩ := han (show 2018 ≥ 2 by simp)
          rw [han]
          unfold S
          simp at hk
          apply div_le_iff₀ ?_ |>.mpr
          · trans ∑ i ∈ Icc 1 k, 1
            apply sum_le_sum
            intro i hi
            simp at hi
            by_cases hi' : i = 2018
            · simp [hi', ha0]
            · rw [hne]
              · suffices h : 0 < 2018 - i
                · exact h
                · apply Nat.lt_sub_of_add_lt
                  simp
                  apply lt_of_le_of_ne ?_ hi'
                  apply le_trans hi.2 hk.2
              · apply Nat.sub_le_of_le_add
                linarith only [hi.1]
            simp
          · simp
            exact hk.1
        · rw [hne]
          · simp
          · simp
      · norm_num
    · -- Therefore, $$ a_{2018}-a_{2017} \leqslant M_{2018}-m_{2018}=\Delta_{2018}, $$ and we are interested in an upper bound for $\Delta_{2018}$.
      trans Δ 2018 (by simp)
      · apply sub_le_sub
        · apply ha_n_le
          simp
        · apply ha_n_sub_one_ge
          simp
      · -- Otherwise, let $2 \leqslant q \leqslant 2017$ be the minimal index with $a_{q}<1$.
        push_neg at hne
        let q : ℕ := set_of_ne_one.min' hne
        have hq_ge : 2 ≤ q := by
          obtain h : q ∈ set_of_ne_one := min'_mem _ hne
          simp [set_of_ne_one] at h
          obtain h' := h.1.1
          by_contra h''
          simp at h''
          interval_cases q
          simp [ha1] at h
        have hq_le : q ≤ 2017 := by
          obtain h : q ∈ set_of_ne_one := min'_mem _ hne
          simp [set_of_ne_one] at h
          exact h.1.2
        have ha_q_lt_1 : a q ≠ 1 := by
          obtain h : q ∈ set_of_ne_one := min'_mem _ hne
          simp [set_of_ne_one] at h
          exact h.2
        have heq_1_of_lt_q {i : ℕ} (hi : i ∈ Ico 1 q) : a i = 1 := by
          suffices h : i ∉ set_of_ne_one
          · simp [set_of_ne_one] at h
            simp at hi
            apply h hi.1
            apply le_trans ?_ hq_le
            apply le_of_lt hi.2
          · by_contra h
            have : i ≥ q := by apply min'_le; exact h
            simp at hi
            linarith only [this, hi.2]
        -- We have $S(q, i)=i$ for all $i=1,2, \ldots, q-1$, while $S(q, q)=q-1$.
        -- Therefore, $a_{q}<1$ yields $a_{q}=S(q, q) / q=1-\frac{1}{q}$.
        have ha_q_eq : a q = 1 - 1 / q := by
          obtain ⟨k, hk, haq⟩ := han hq_ge
          simp [haq, S]
          by_cases hk' : k < q
          · have : a q = 1 := by
              simp [haq, S]
              trans (∑ i ∈ Icc 1 k, 1) / (k : ℝ)
              · congr 1
                apply sum_congr rfl
                by_contra h
                push_neg at h
                obtain ⟨i, hi, ha⟩ := h
                have : q - i ∈ set_of_ne_one := by
                  simp [set_of_ne_one, ha]
                  constructor
                  · refine Nat.succ_le_of_lt ?_
                    apply Nat.sub_pos_of_lt
                    apply lt_of_le_of_lt ?_ hk'
                    simp at hi
                    exact hi.2
                  · apply le_trans hq_le
                    exact Nat.le_add_right 2017 i
                have h₁ : q ≤ q - i := by
                  apply min'_le
                  exact this
                have h₂ : q - i < q := by
                  refine Nat.sub_lt ?_ ?_
                  · exact Nat.zero_lt_of_lt hq_ge
                  · simp at hi
                    apply Nat.zero_lt_of_lt hi.1
                linarith only [h₁, h₂]
              · simp at hk
                simp
                have : (k : ℝ) ≠ 0 := by simp; apply ne_of_gt; exact hk.1
                field_simp
            simp [this] at ha_q_lt_1
          · push_neg at hk'
            have hk : k = q := by
              apply le_antisymm ?_ hk'
              simp at hk
              exact hk.2
            rw [hk, Icc_eq_cons_Ico, sum_cons]
            simp [ha0]
            trans (∑ x ∈ Ico 1 q, 1 : ℝ) / (q : ℝ)
            · congr 1
              apply sum_congr rfl
              intro i hi
              apply heq_1_of_lt_q
              simp at hi ⊢  
              constructor
              · exact Nat.le_sub_of_add_le' hi.2
              · constructor
                · exact Nat.zero_lt_of_lt hq_ge
                · exact Nat.zero_lt_of_lt hi.1
            · field_simp
            · exact Nat.one_le_of_lt hq_ge
        -- Now we have $S(q+1, i)=i-\frac{1}{q}$ for $i=1,2, \ldots, q$, and $S(q+1, q+1)=q-\frac{1}{q}$.
        have hS_q_i {i : ℕ} (hi : i ∈ Icc 1 q) : S (q + 1) i = i - 1 / q := by
          simp [S]
          simp at hi
          obtain ⟨hi₁, hi₂⟩ := hi
          rw [Icc_eq_cons_Ioc (by simp [hi₁]), sum_cons]
          simp [ha_q_eq]
          trans 1 - (↑q)⁻¹ + ∑ x ∈ Ioc 1 i, (1 : ℝ)
          · congr 1
            apply sum_congr rfl
            intro x hx
            apply heq_1_of_lt_q
            simp at hx ⊢ 
            obtain ⟨h₁, h₂⟩ := hx
            constructor 
            · apply Nat.le_sub_of_add_le'
              gcongr
              apply le_trans h₂ hi₂
            · apply Nat.sub_lt_right_of_lt_add
              apply le_trans h₂ (le_trans hi₂ ?_)
              simp
              gcongr
          · field_simp
            ring
        have hS_q_q : S (q + 1) (q + 1) = q - 1 / q := by
          simp [S]
          rw [Icc_eq_cons_Ioc (by simp), sum_cons, Ioc_eq_cons_Ioo (by simp; exact Nat.zero_lt_of_lt hq_ge), sum_cons]
          simp [ha_q_eq, ha0]
          trans 1 - (↑q)⁻¹ + ∑ x ∈ Ioo 1 (q + 1), (1 : ℝ)
          · congr 1
            apply sum_congr rfl
            intro x hx
            apply heq_1_of_lt_q
            simp at hx ⊢ 
            obtain ⟨h₁, h₂⟩ := hx
            constructor 
            · apply Nat.le_sub_of_add_le'
              exact h₂
            · apply Nat.sub_lt_left_of_lt_add
              apply le_of_lt h₂
              rw [add_comm]
              gcongr
          · field_simp
            ring
        -- This gives us $$ m_{q+1}=\frac{S(q+1,1)}{1}=\frac{S(q+1, q+1)}{q+1}=\frac{q-1}{q} \quad \text { and } \quad M_{q+1}=\frac{S(q+1, q)}{q}=\frac{q^{2}-1}{q^{2}} $$
        have hm : m (q + 1) (by simp) = (q - 1) / q := by
          unfold m
          apply le_antisymm
          · apply min'_le
            simp
            use 1
            simp
            rw [hS_q_i]
            · field_simp
            · simp
              exact Nat.one_le_of_lt hq_ge
          · apply le_min'
            simp
            intro y i hi₁ hi₂ hy
            rw [←hy]
            by_cases hi : i ≤ q
            · rw [hS_q_i]
              apply sub_nonneg.mp
              field_simp
              apply div_nonneg
              · ring_nf
                trans q * (i - 1 : ℝ)
                · apply mul_nonneg
                  · simp
                  · simp [hi₁]
                · apply le_of_eq
                  ring
              · norm_cast
                positivity
              · simp [hi₁, hi]
            · have : i = q + 1 := by
                apply le_antisymm hi₂
                simp at hi
                exact hi
              rw [this, hS_q_q]
              apply sub_nonneg.mp
              field_simp
              apply div_nonneg
              · apply le_of_eq
                ring
              · norm_cast
                positivity
        have hM : M (q + 1) (by simp) = (q ^ 2 - 1) / q ^ 2 := by
          unfold M
          apply le_antisymm
          · apply max'_le
            intro y hy
            simp at hy
            obtain ⟨a, ⟨h₁, h₂⟩, hSa⟩ := hy
            rw [←hSa]
            by_cases ha : a ≤ q
            · rw [hS_q_i]
              · field_simp
                apply div_le_div_iff₀ ?_ ?_ |>.mpr
                · apply sub_nonneg.mp
                  ring_nf
                  trans q * (q - a : ℝ)
                  · apply mul_nonneg
                    · simp
                    · simp [ha]
                  · apply le_of_eq
                    ring
                · apply mul_pos
                  · simp; exact Nat.zero_lt_of_lt hq_ge 
                  · simp; exact h₁
                · apply sq_pos_of_pos
                  simp
                  exact Nat.zero_lt_of_lt hq_ge 
              · simp [h₁, ha]
            · simp at ha
              have : q + 1 = a := by 
                apply le_antisymm
                · exact ha
                · exact h₂
              rw [←this, hS_q_q]
              field_simp
              apply div_le_div_iff₀ ?_ ?_ |>.mpr
              · apply sub_nonneg.mp
                ring_nf
                trans q * (q - 1) * (q + 1 : ℝ)
                · apply mul_nonneg
                  · apply mul_nonneg
                    · simp
                    · simp
                      exact Nat.one_le_of_lt hq_ge
                  · norm_cast
                    simp
                · apply le_of_eq
                  ring
              · norm_cast
                positivity
              · norm_cast
                positivity
          · apply le_max'
            simp
            use q
            simp
            constructor
            · exact Nat.one_le_of_lt hq_ge
            · rw [hS_q_i]
              field_simp
              ring
              simp
              exact Nat.one_le_of_lt hq_ge
        -- so $\Delta_{q+1}=M_{q+1}-m_{q+1}=(q-1) / q^{2}$.
        have hΔ : Δ (q + 1) (by simp) = (q - 1) / q ^ 2 := by
          unfold Δ
          rw [hM, hm]
          field_simp
          ring
        -- Denoting $N=2017 \geqslant q$ and using Claim 1 for $n=q+2, q+3, \ldots, N+1$
        -- we finally obtain $$ \Delta_{N+1} \leqslant \frac{q-1}{q^{2}} \cdot \frac{q+1}{q+2} \cdot \frac{q+2}{q+3} \cdots \frac{N}{N+1}=\frac{1}{N+1}\left(1-\frac{1}{q^{2}}\right) \leqslant \frac{1}{N+1}\left(1-\frac{1}{N^{2}}\right)=\frac{N-1}{N^{2}} $$ as required.
        have Δ_le {N : ℕ} (hN : N ≥ q) : Δ (N + 1) (by simp) ≤ 1 / (N + 1) * (1 - 1 / q ^ 2) := by
          induction N, hN using Nat.le_induction
          · rw [hΔ]
            apply le_of_eq
            field_simp
            ring
          · rename_i N hN ih
            apply le_trans (hclaim _ ?_)
            · simp
              trans (↑N + 1) / (↑N + 1 + 1) * (1 / (↑N + 1) * (1 - 1 / ↑q ^ 2) : ℝ)
              · apply mul_le_mul_of_nonneg_left
                · exact ih
                · norm_cast
                  positivity
              · apply le_of_eq
                field_simp
                ring
            · simp
              apply lt_of_lt_of_le ?_ hN
              apply lt_of_lt_of_le ?_ hq_ge 
              simp
        apply le_trans (Δ_le ?_)
        · trans 1 / (2017 + 1) * (1 - 1 / 2017 ^ 2 : ℝ)
          · gcongr
            simp [hq_le]
          · apply le_of_eq
            ring
        · exact hq_le
