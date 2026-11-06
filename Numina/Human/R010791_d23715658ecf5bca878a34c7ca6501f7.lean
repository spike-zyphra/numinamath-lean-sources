import Mathlib

open Finset Real

/- Soient $b_{1}, \ldots, b_{n}$ des réels positifs ou nuls tels que $b_{1}+b_{2}+\ldots+b_{n}=2$. Soient $a_{0}, a_{1}, \ldots, a_{n}$ des nombres réels tels que $a_{0}=a_{n}=0$. Supposons que pour tout $i$ compris entre 1 et $n$ inclus,

$$
\left|a_{i}-a_{i-1}\right| \leqslant b_{i}
$$

Montrer que l'on a

$$
\left(a_{0}+a_{1}\right) b_{1}+\left(a_{1}+a_{2}\right) b_{2}+\ldots+\left(a_{n-1}+a_{n}\right) b_{n} \leqslant 2
$$ -/
theorem inequalities_607362 {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ)
    (hb : ∀ i ∈ Icc 1 n, 0 ≤ b i) (hsum : ∑ i ∈ Icc 1 n, b i = 2)
    (a : ℕ → ℝ) (ha : a 0 = 0) (ha' : a n = 0)
    (h : ∀ i ∈ Icc 1 n, |a i - a (i - 1)| ≤ b i) :
    ∑ i ∈ Icc 1 n, (a i + a (i - 1)) * b i ≤ 2 := by

  -- Pour tout indice $i$, on a deux majorations de $a_{i}$. En effet, on peut écrire
  -- $$ \begin{aligned} a_{i}=a_{i}-a_{0}= & \left(a_{i}-a_{i-1}\right)+\left(a_{i-1}-a_{i-2}\right)+\ldots+\left(a_{1}-a_{0}\right) \ & \leqslant b_{i}+b_{i-1}+\ldots+b_{1}=\sum_{j=1}^{i} b_{j} \end{aligned} $$
  have hsum_Icc' {i j : ℕ} {f : ℕ → ℝ} (h : i ≤ j) : ∑ k ∈ Icc i j, f k = f i + ∑ k ∈ Icc (i + 1) j, f k := by
    rw [Icc_eq_cons_Ioc h, sum_cons]
    congr
    ext k
    simp
    tauto
  have hale {i : ℕ} (hi : i ∈ Icc 0 n) : a i ≤ ∑ j ∈ Icc 1 i, b j := by
    induction i with
    | zero => simp [ha]
    | succ j ih =>
      by_cases hj : j + 1 ∈ Icc 1 n
      · have hj' : j ∈ Icc 0 n := by
          simp at hj ⊢
          exact Nat.le_of_succ_le hj
        apply ih at hj'
        calc
          _ = a j + (a (j + 1) - a j) := by ring
          _ ≤ ∑ j ∈ Icc 1 j, b j + b (j + 1) := by
            apply add_le_add hj'
            obtain h := h (j + 1) hj
            rw [Nat.add_sub_cancel] at h
            exact le_of_max_le_left h
          _ = _ := by
            rw [sum_Icc_succ_top]
            exact Nat.le_add_left 1 j
      · simp at hi hj
        have : n > n := by apply lt_of_lt_of_le hj hi
        linarith only [this]
  -- et $$ \begin{aligned} a_{i}=a_{i}-a_{n} & =\left(a_{i}-a_{i+1}\right)-\left(a_{i+1}-a_{i+2}\right)+\ldots+\left(a_{n-1}-a_{n}\right) \ & \leqslant b_{i+1}+b_{i+2}+\ldots+b_{n}=\sum_{j=i+1}^{n} b_{j} \end{aligned} $$
  have hale' {i : ℕ} (hi : i ∈ Icc 0 n) : a i ≤ ∑ j ∈ Icc (i + 1) n, b j := by
    simp at hi
    induction hi using Nat.decreasingInduction
    · rename_i k hlt hle
      calc
        _ = a (k + 1) + -(a (k + 1) - a k) := by ring
        _ ≤ ∑ j ∈ Icc (k + 1 + 1) n, b j + b (k + 1) := by
          apply add_le_add hle
          have : k + 1 ∈ Icc 1 n := by
            simp
            exact hlt
          apply h (k + 1) at this
          rw [Nat.add_sub_cancel] at this
          exact le_of_max_le_right this
        _ = _ := by
          nth_rw 2 [hsum_Icc']
          · ring
          · exact hlt
    · simp [ha']

  -- Afin de majorer efficacement $a_{i}$, on voudrait trouver le plus petit de ces deux termes.
  -- Mais la somme des deux vaut 2 , donc il faut simplement déterminer si $\sum_{j=1}^{i} b_{j}$ est inférieur ou supérieur à 1 .
  have p : ∃ i ∈ Icc 1 n, ∑ j ∈ Icc 1 i, b j > 1 := by
      use n
      simp
      constructor
      · exact hn
      · simp [hsum]
  -- Soit $m$ l'entier minimal tel que $\sum_{j=1}^{m} b_{j}&gt;1$.
  let m := Nat.find p
  have hm : m ∈ Icc 1 n ∧ ∑ j ∈ Icc 1 m, b j > 1 := Nat.find_spec p
  obtain ⟨hm1, hm2⟩ := hm
  simp at hm1
  obtain ⟨hmge, hmle⟩ := hm1

  -- On écrit alors
  -- $$ \sum_{i=1}^{n}\left(a_{i-1}+a_{i}\right) b_{i}=\sum_{i=1}^{m-1}\left(a_{i-1}+a_{i}\right) b_{i}+\left(a_{m-1}+a_{m}\right) b_{m}+\sum_{i=m+1}^{n}\left(a_{i-1}+a_{i}\right) b_{i} $$
  have heq : ∑ i ∈ Icc 1 n, (a i + a (i - 1)) * b i = ∑ i ∈ Icc 1 (m - 1), (a i + a (i - 1)) * b i + (a (m - 1) + a m) * b m + ∑ i ∈ Icc (m + 1) n, (a i + a (i - 1)) * b i := by
    have : Icc 1 n = Icc 1 (m - 1) ∪ {m} ∪ Icc (m + 1) n := by
      ext i
      simp
      constructor <;> intro h
      · simp [h]
        by_cases h : i = m
        · simp [h]
        · simp [h]
          rcases lt_or_gt_of_ne h with h | h
          · apply Or.inl
            exact Nat.le_sub_one_of_lt h
          · apply Or.inr
            exact Nat.succ_le_of_lt h
      · rcases h with h | h | h
        · simp [h.1]
          apply le_trans h.2
          apply le_trans ?_ hmle
          exact Nat.sub_le m 1
        · simp [h]
          exact ⟨hmge, hmle⟩
        · simp [h.2]
          apply le_trans ?_ h.1
          exact Nat.le_add_right_of_le hmge
    rw [this, sum_union, sum_union]
    · simp
      apply Or.inl
      ring
    · simp
      intro _
      exact hmge
    · intro S hS1 hS2 i hi
      obtain h1 := hS1 hi
      obtain h2 := hS2 hi
      simp at h1 h2
      have : i ≤ m := by
        rcases h1 with h | h
        · apply le_trans h.2
          exact Nat.sub_le m 1
        · simp [h]
      have : ¬ i ≤ m := by
        simp
        linarith only [h2.1]
      contradiction
  rw [heq]

  -- Pour $i&lt;m$, on majore $a_{i}$ par $\sum_{j=1}^{i} b_{j}$, et pour $i \geqslant m$,
  -- on majore $a_{i}$ par $\sum_{j=i+1}^{n} b_{j}$ pour obtenir $\sum_{i=1}^{n}\left(a_{i-1}+a_{i}\right) b_{i} \leqslant \sum_{i=1}^{m-1}\left(b_{i}+2 \sum_{j=1}^{i-1} b_{j}\right) b_{i}+\left(\sum_{j=1}^{m-1} b_{j}+\sum_{j=m+1}^{n} b_{j}\right) b_{m}+\sum_{i=1}^{m}\left(b_{i}+2 \sum_{j=i+1}^{n} b_{j}\right) b_{i}$.
  have : ∑ i ∈ Icc 1 (m - 1), (a i + a (i - 1)) * b i + (a (m - 1) + a m) * b m + ∑ i ∈ Icc (m + 1) n, (a i + a (i - 1)) * b i ≤
    ∑ i ∈ Icc 1 (m - 1), (b i + 2 * ∑ j ∈ Icc 1 (i - 1), b j) * b i + (∑ j ∈ Icc 1 (m - 1), b j + ∑ j ∈ Icc (m + 1) n, b j) * b m + ∑ i ∈ Icc (m + 1) n, (b i + 2 * ∑ j ∈ Icc (i + 1) n, b j) * b i := by
      apply add_le_add
      · apply add_le_add
        · apply sum_le_sum
          intro i hi
          simp at hi
          apply mul_le_mul_of_nonneg_right
          · have hiin : i ∈ Icc 0 n := by
              simp
              apply le_trans hi.2
              apply le_trans ?_ hmle
              exact Nat.sub_le m 1
            have hisub : i - 1 ∈ Icc 0 n := by
              simp at hiin ⊢
              exact Nat.le_add_right_of_le hiin
            calc
              _ ≤ ∑ j ∈ Icc 1 i, b j + ∑ j ∈ Icc 1 (i - 1), b j := by rel [hale hiin, hale hisub]
              _ = _ := by
                have : i = i - 1 + 1 := by rw [Nat.sub_add_cancel hi.1]
                rw [this, sum_Icc_succ_top, ←this]
                ring
                rw [←this]
                exact hi.1
          · apply hb
            simp [hi.1]
            apply le_trans hi.2
            apply le_trans ?_ hmle
            exact Nat.sub_le m 1
        · apply mul_le_mul_of_nonneg_right
          · apply add_le_add
            · apply hale
              simp
              exact Nat.le_add_right_of_le hmle
            · apply hale'
              simp
              exact hmle
          · apply hb
            simp
            exact ⟨hmge, hmle⟩
      · apply sum_le_sum
        intro i hi
        simp at hi
        apply mul_le_mul_of_nonneg_right
        · have hige : i ≥ 1 := by
            apply le_trans ?_ hi.1
            exact Nat.le_add_right_of_le hmge
          have hi1 : i ∈ Icc 0 n := by
            simp
            exact hi.2
          have hi2 : i - 1 ∈ Icc 0 n := by
            simp
            apply le_trans hi.2
            exact Nat.le_add_right n 1
          calc
            _  ≤ ∑ j ∈ Icc (i + 1) n, b j + ∑ j ∈ Icc i n, b j := by
                nth_rw 4 [←Nat.sub_add_cancel hige]
                rel [hale' hi1, hale' hi2]
            _ = _ := by
                nth_rw 2 [hsum_Icc']
                ring
                exact hi.2
        · apply hb
          simp
          constructor
          · apply le_trans ?_ hi.1
            exact Nat.le_add_right_of_le hmge
          · exact hi.2
  apply le_trans this
  -- Posons $x=\sum_{j=1}^{m-1} b_{j}$ et $y=\sum_{j=m+1}^{n} b_{j}$.
  let x := ∑ j ∈ Icc 1 (m - 1), b j
  let y := ∑ j ∈ Icc (m + 1) n, b j
  -- Par définition de $m$, on a $x \leqslant 1$ et $y \leqslant 1$.
  have hx : x ≤ 1 := by
    simp [x]
    have hmin : m - 1 < m := by exact Nat.sub_one_lt_of_lt hmge
    apply Nat.find_min p at hmin
    by_cases hm : m ≥ 2
    · have : m - 1 ∈ Icc 1 n := by
        simp
        constructor
        · exact (Nat.le_sub_one_iff_lt hmge).mpr hm
        · apply le_trans hmle
          exact Nat.le_add_right n 1
      simp [this] at hmin
      exact hmin
    · simp at hm
      interval_cases m
      simp
  have hxadd : x + b m = ∑ j ∈ Icc 1 m, b j := by
    simp [x]
    nth_rw 2 [←Nat.sub_add_cancel hmge]
    rw [←sum_Icc_succ_top]
    rw [Nat.sub_add_cancel hmge]
    exact Nat.le_add_left 1 (m - 1)
  -- On peut donc écrire, comme $x+b_{m}+y=2$,
  have hxaddy : x + b m + y = 2 := by
    rw [hxadd, ←hsum]
    simp [y]
    have : Icc 1 n = Icc 1 m ∪ Icc (m + 1) n := by
      ext i
      simp
      constructor <;> intro h
      · simp [h]
        by_cases h : i ≤ m
        · apply Or.inl
          exact h
        · apply Or.inr
          push_neg at h
          exact h
      · rcases h with h | h
        · simp [h.1]
          apply le_trans h.2 hmle
        · simp [h.2]
          apply le_trans ?_ h.1
          exact Nat.le_add_right_of_le hmge
    rw [this, sum_union]
    intro S hS1 hS2 i hi
    obtain h1 := hS1 hi
    obtain h2 := hS2 hi
    simp at h1 h2
    have : m + 1 ≤ m := by apply le_trans h2.1 h1.2
    linarith only [this]
  have hbm : b m = 2 - (x + y) := by
    rw [←hxaddy]
    ring
  have hxadd : x + b m > 1 := by
    rw [hxadd]
    exact hm2
  have hy : y ≤ 1 := by
    calc
      y = 2 - (x + b m) := by rw [←hxaddy]; ring
      _ ≤ 2 - 1 := by rel [hxadd]
      _ = 1 := by ring
  -- Considérons la première somme dans le terme précédent.
  -- Dans celle-ci, on a un terme $b_{i}^{2}$ pour tout $i \leqslant m-1$ et un terme $2 b_{i} b_{j}$ pour tous $j&lt;i \leqslant m-1$.
  -- Ainsi, cette somme n'est rien d'autre que $x^{2}$.
  have hsumsq {i : ℕ}: (∑ j ∈ Icc 1 i, b j) ^ 2 = ∑ j ∈ Icc 1 i, b j ^ 2 + 2 * ∑ j ∈ Icc 1 i, (∑ k ∈ Icc 1 (j - 1), b k) * b j := by
    induction i with
    | zero => simp
    | succ i' ih =>
      have : 1 ≤ i' + 1 := by exact Nat.le_add_left 1 i'
      rw [sum_Icc_succ_top this, add_sq, ih, sum_Icc_succ_top this, sum_Icc_succ_top this, mul_add, Nat.add_sub_cancel]
      ring
  have hxsq : x ^ 2 = ∑ i ∈ Icc 1 (m - 1), (b i + 2 * ∑ j ∈ Icc 1 (i - 1), b j) * b i := by
    simp only [x]
    rw [hsumsq, mul_sum, ←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [add_mul]
    ring
  have hsumsq' {i : ℕ} (hi : i ≤ n + 1): (∑ j ∈ Icc i n, b j) ^ 2 = ∑ j ∈ Icc i n, b j ^ 2 + 2 * ∑ j ∈ Icc i n, (∑ k ∈ Icc (j + 1) n, b k) * b j := by
    induction hi using Nat.decreasingInduction
    · rename_i i' hi' ih
      have : i' ≤ n := by exact Nat.le_of_lt_succ hi'
      rw [hsum_Icc' this, add_sq, hsum_Icc' this, hsum_Icc' this, ih]
      ring
    · simp
  -- De même, la somme de droite n'est rien d'autre que $y^{2}$.
  have hysq : y ^ 2 = ∑ i ∈ Icc (m + 1) n, (b i + 2 * ∑ j ∈ Icc (i + 1) n, b j) * b i := by
    simp only [y]
    rw [hsumsq']
    · rw [mul_sum, ←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [add_mul]
      ring
    · exact Nat.add_le_add_right hmle 1
  -- $$ \begin{aligned} \sum_{i=1}^{n}\left(a_{i-1}+a_{i}\right) b_{i} & \leqslant x^{2}+(x+y)(2-x-y)+y^{2} \ = & 2(x+y)-2 x y \end{aligned} $$
  rw [←hxsq, ←hysq]
  calc
    -- Il nous reste enfin à voir que $2(x+y)-2 x y \leqslant 2$ pour conclure,
    -- ou encore $x+y-x y \leqslant 1$. Mais ceci se réécrit, en passant tous les termes à droite de l'inégalité,
    _ = x ^ 2 + y ^ 2 + (x + y) * (2 - x - y) := by
      rw [hbm]
      ring
    _ = 2 -2 * (1 - x) * (1 - y) := by ring
    _ ≤ 2 := by
      -- $$ (1-x)(1-y) \geqslant 0 $$
      -- ce qui est vérifié car on a vu que $x \leqslant 1$ et $y \leqslant 1$.
      simp
      apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact sub_nonneg_of_le hx
      · exact sub_nonneg_of_le hy
