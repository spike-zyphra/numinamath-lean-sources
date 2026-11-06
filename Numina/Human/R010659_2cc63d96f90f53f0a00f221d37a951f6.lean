import Mathlib

open Real

set_option maxHeartbeats 1000000

/- Soit $n \geqslant 3$ un entier, et $x_{1}, x_{2}, \ldots, x_{n}$ des nombres réels appartenant à l'intervalle $[0,1]$.
  On suppose que la somme $s=x_{1}+x_{2}+\cdots+x_{n}$ vérifie l'inégalité $s \geqslant 3$.
  Démontrer qu'il existe des entiers $i$ et $j$ tels que $2^{j-i} x_{i} x_{j}>2^{s-3}$. -/
theorem inequalities_605762 (n : ℕ) (hn : 3 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc 0 1) (hsum : ∑ i, x i ≥ 3) :
    ∃ i j, 2^ (j.1 - i.1 : ℝ) * x i * x j > 2 ^ (∑ i, x i - 3) := by

  -- In the following, we set $x_{t}=0$ if $t \leqslant 0$ or $t \geqslant n+1$, which does not change the problem.
  -- Let $u$ and $v$ be two indices for which $2^{u-v} x_{u} x_{v}$ is maximal.
  let f (p : Fin n × Fin n) := 2 ^ (p.1.1 - p.2.1 : ℝ) * x p.1 * x p.2
  have img_ne : (Finset.image f Finset.univ).Nonempty := by
    simp
    use (⟨0, by exact Nat.zero_lt_of_lt hn⟩, ⟨0, by exact Nat.zero_lt_of_lt hn⟩)
    simp
  let r := (Finset.univ.image f).max' img_ne
  have hr : r ∈ Finset.univ.image f := by exact Finset.max'_mem (Finset.image f Finset.univ) img_ne
  simp at hr
  obtain ⟨u, v, huv⟩ := hr
  simp [f] at huv
  use v, u
  rw [mul_assoc]
  nth_rw 2 [mul_comm]
  rw [←mul_assoc]
  rw [huv]

  -- This product is at least $\max \left\{x_{i}^{2}\right\} \geqslant(s / n)^{2}$, so it is non-zero, meaning that $x_{u}$ and $x_{v}$ are non-zero.
  have hune : x u > 0 := by
    by_contra h
    simp at h
    obtain h' := hx u
    simp at h'
    apply le_antisymm h'.1 at h
    simp [←h] at huv
    have : ∑ i, x i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : 2 ^ (i.1 - i.1) * x i * x i ≤ 0 := by
        rw [huv]
        apply Finset.le_max'
        simp [f]
        use i, i
        simp
      simp at this
      have hge : x i * x i ≥ 0 := by exact mul_self_nonneg (x i)
      apply le_antisymm this at hge
      simp at hge
      exact hge
    rw [this] at hsum
    linarith
  -- x v > 0
  have hvne : x v > 0 := by
    by_contra h
    simp at h
    obtain h' := hx v
    simp at h'
    apply le_antisymm h'.1 at h
    simp [←h] at huv
    have : ∑ i, x i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : 2 ^ (i.1 - i.1) * x i * x i ≤ 0 := by
        rw [huv]
        apply Finset.le_max'
        simp [f]
        use i, i
        simp
      simp at this
      have hge : x i * x i ≥ 0 := by exact mul_self_nonneg (x i)
      apply le_antisymm this at hge
      simp at hge
      exact hge
    rw [this] at hsum
    linarith
  -- By definition, we know that $\max \left\{2^{u-t} x_{u} x_{t}, 2^{t-v} x_{t} x_{v}\right\} \leqslant 2^{u-v} x_{u} x_{v}$,
  have hmax (t : Fin n) : max (2 ^ (u.1 - t.1 : ℝ) * x u * x t) (2 ^ (t.1 - v.1 : ℝ) * x t * x v) ≤ r := by
    simp
    constructor <;> (apply Finset.le_max'; simp [f])
  -- that is, $x_{t} \leqslant \min \left\{1,2^{u-t} x_{u}, 2^{t-v} x_{v}\right\}$, for any integer $t$.
  have hxt_le_one {t : Fin n} : x t ≤ 1 := by simp at hx; exact (hx t).2
  have hxt_le {t : Fin n} : x t ≤ min (2 ^ (u.1 - t.1 : ℝ) * x u) (2 ^ (t.1 - v.1 : ℝ) * x v) := by
    simp
    obtain ⟨h1, h2⟩ := max_le_iff.mp <| hmax t
    rw [←huv] at h1 h2
    constructor
    · calc
        _ = 2 ^ (t.1 - ↑v : ℝ) * x v * x t / (2 ^ (t.1 - ↑v : ℝ) * x v) := by
          rw [mul_div_cancel_left₀]
          simp
          constructor
          · apply ne_of_gt
            apply rpow_pos_of_pos
            norm_num
          · exact ne_of_gt hvne
        _ = 2 ^ (↑t - ↑v : ℝ) * x t * x v / (2 ^ (t.1 - ↑v : ℝ) * x v) := by ring
        _ ≤ 2 ^ (↑u - ↑v : ℝ) * x u * x v / (2 ^ (t.1 - ↑v : ℝ) * x v) := by rel [h2]
        _ = _ := by
          rw [rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp)]
          field_simp
          ring
    · calc
        _ = 2 ^ (u.1 - t.1 : ℝ) * x u * x t / (2 ^ (u.1 - t.1 : ℝ) * x u) := by
          rw [mul_div_cancel_left₀]
          simp
          constructor
          · apply ne_of_gt
            apply rpow_pos_of_pos
            norm_num
          · exact ne_of_gt hune
        _ = 2 ^ (↑u - ↑t : ℝ) * x u * x t / (2 ^ (u.1 - t.1 : ℝ) * x u) := by ring
        _ ≤ 2 ^ (↑u - ↑v : ℝ) * x u * x v / (2 ^ (u.1 - t.1 : ℝ) * x u) := by rel [h1]
        _ = _ := by
          rw [rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp)]
          field_simp
          ring
  -- Furthermore, there exists a real number $\tau$ such that $2^{u-\tau} x_{u}=2^{\tau-v} x_{v}$: this is the real number
  -- $$ \tau=\frac{u+v+\log _{2}\left(x_{u} / x_{v}\right)}{2} $$
  let τ := (u.1 + v.1 + logb 2 (x u / x v)) / 2
  have hτ : 2 ^ (u.1 - τ) * x u = 2 ^ (τ - v.1) * x v := by
    simp [τ]
    rw [rpow_sub (by simp), rpow_sub (by simp)]
    simp [rpow_div_two_eq_sqrt, rpow_add]
    field_simp
    ring_nf
    have {x : ℕ} : √2 ^ (x * 2) = 2 ^ x := by rw [mul_comm, pow_mul]; norm_num
    simp [this]
    ring_nf
    congr
    rw [←rpow_natCast, ←rpow_mul (by simp), mul_comm _ ((2 : ℕ) : ℝ), rpow_mul (by simp)]
    simp
    rw [rpow_logb (by simp) (by simp), mul_comm, mul_assoc, inv_mul_cancel₀ (by exact ne_of_gt hvne), mul_one]
    apply mul_pos hune
    apply inv_pos.mpr hvne
  -- We then set $\alpha=2^{u-\tau} x_{u}=2^{\tau-v} x_{v}$, that is, $\alpha=2^{(u-v) / 2} \sqrt{x_{u} x_{v}}$,
  let α := 2 ^ (u.1 - τ) * x u
  have hαpos : α > 0 := by
    apply mul_pos
    · apply rpow_pos_of_pos
      norm_num
    · exact hune
  have hr : r = α ^ 2 := by
    rw [sq]
    simp [α]
    nth_rw 1 [hτ]
    rw [←huv, rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp)]
    field_simp
    ring
  -- It suffices to probe s  - 3 < 2 * log₂ α
  rw [hr]
  apply logb_lt_logb_iff (b := 2) (by simp) (by apply rpow_pos_of_pos; simp) (sq_pos_of_pos hαpos) |>.mp
  rw [logb_rpow (by simp) (by simp), logb_pow]
  simp

  -- and we easily verify that $x_{t} \leqslant \alpha / 2^{|t-\tau|}$ for any integer $t$.
  have hxt_le_τ {t : Fin n} : x t ≤ min (α / 2 ^ (t.1 - τ)) (α / 2 ^ (τ - t.1)) := by
    apply le_trans hxt_le
    simp
    constructor
    · left; simp [α]
      apply le_of_eq
      rw [rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp)]
      field_simp
    · right; simp [α, hτ]
      apply le_of_eq
      rw [rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp)]
      field_simp
      ring
  -- Now let $w=\tau-\lfloor\tau\rfloor$, so that $0 \leqslant w \leqslant 1$.
  let w := τ - ⌊τ⌋
  have hwnonneg : 0 ≤ w := by simp [w]
  have hwlt : w < 1 := by simp [w]; exact Int.fract_lt_one τ
  -- Since the function $f: x \mapsto 2^{x}+2^{1-x}$ is convex and $f(0)=f(1)=3$, we then have
  let f (x : ℝ) := (2 : ℝ) ^ x + 2 ^ (1 - x)
  have hf : f w ≤ 3 := by
    simp [f]
    suffices h : ((2 : ℝ) ^ w - 1) * (2 ^ w - 2) ≤ 0
    · calc
        _ = ((2 : ℝ) ^ w - 1) * (2 ^ w - 2) / 2 ^ w + 3 := by rw [rpow_sub (by simp) 1 w]; field_simp; ring
        _ ≤ 0 / 2 ^ w + 3 := by rel [h]
        _ = 3 := by simp
    · apply mul_nonpos_of_nonneg_of_nonpos
      · simp
        apply one_le_rpow ?_ hwnonneg
        simp
      · simp
        nth_rw 2 [←rpow_one 2]
        apply rpow_le_rpow_of_exponent_le
        · simp
        · exact le_of_lt hwlt
  -- $$ 3 \leqslant s=\sum_{t \leqslant \tau-w} x_{t}+\sum_{t \geqslant \tau+1-w} x_{t}
  let s := ∑ i, x i
  have hseq : s = ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ ⌊τ⌋), x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ ⌊τ⌋ + 1), x i := by
    simp [s]
    rw [←Finset.sum_union]
    · congr
      ext i
      simp
      by_cases h : i.val ≤ ⌊τ⌋
      · simp [h]
      · simp at h
        right
        exact h
    · refine Finset.disjoint_filter.mpr ?_
      intro x _ hx
      simp [hx]
      exact Int.lt_add_one_iff.mpr hx
  have hgeom {k : ℕ} : ∑ i ∈ Finset.Icc (0 : ℤ) k, (1 / 2 : ℝ) ^ i < 2 := by
    calc
      _ = ∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i := by
          let f (x : ℤ) : ℕ := x.natAbs
          have : (Finset.Icc (0 : ℤ) k).image f = Finset.range (k + 1) := by
            ext i
            simp [f]
            constructor <;> intro h
            · obtain ⟨j, h1, h2⟩ := h
              simp [←h2]
              rw [←Int.natAbs_of_nonneg h1.1] at h1
              simp at h1
              have : (j.natAbs : ℤ) < k + 1 := by
                simp
                exact Int.lt_add_one_iff.mpr h1
              norm_cast at this
            · use |i|
              simp
              exact Nat.le_of_lt_succ h
          rw [←this, Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro i hi
            simp [f]
            simp at hi
            rw [←zpow_natCast, Int.natAbs_of_nonneg hi.1]
          · intro x hx y hy h
            simp at hx hy
            simp [f] at h
            rw [←Int.natAbs_of_nonneg hx.1, ←Int.natAbs_of_nonneg hy.1]
            norm_cast
      _ < ∑ i ∈ Finset.range (k + 1 + 1), (1 / 2 : ℝ) ^ i := by
        apply Finset.sum_lt_sum_of_subset (i := k + 1)
        · intro i hi; simp at hi ⊢; apply lt_trans hi; simp
        · simp
        · simp
        · apply pow_pos; simp
        · intro j _ _; apply pow_nonneg; simp
      _ ≤ ∑' i, (1 / 2 : ℝ) ^ i := by
        apply sum_le_tsum
        · intro i _
          apply pow_nonneg
          simp
        · exact summable_geometric_two
      _ = 2 := by exact tsum_geometric_two
  -- calculate the geometric series
  have hlek {k : ℤ} : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), x i < 2 * α * 2 ^ (k - τ) := by
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), (2 : ℝ) ^ (i.val - k) < 2 := by
      calc
        _ = ∑ i ∈ Finset.Icc (max 0 (k - n + 1)) k, (1 / 2 : ℝ) ^ i := by
          let f (i : Fin n) : ℤ := k - i.val
          have : (Finset.univ.filter (fun i : Fin n => i.val ≤ k)).image f = Finset.Icc (max 0 (k - n + 1)) k := by
            ext i
            simp [f]
            constructor <;> intro h
            · obtain ⟨j, h1, h2⟩ := h
              simp [←h2, h1]
              calc
                k - n + 1 = k - (n - 1) := by ring
                _ ≤ _ := by
                  apply sub_le_sub (by simp)
                  apply Int.le_sub_one_of_lt
                  norm_cast
                  exact j.2
            · let a := k - i
              have : a ≥ 0 := by simp [a]; exact h.2
              have ha : a.natAbs < (n : ℤ) := by
                simp [Int.natAbs_of_nonneg this, a]
                calc
                  k - i = k - n + 1 + n - 1 - i := by ring
                  _ ≤ i + n - 1 - i := by rel [h.1.2]
                  _ = n - 1 := by ring
                  _ < n := by simp
              norm_cast at ha
              use ⟨a.natAbs, ha⟩
              constructor
              · simp [Int.natAbs_of_nonneg this, a, h.1.1]
              · simp [Int.natAbs_of_nonneg this, a]
          rw [←this, Finset.sum_image]
          · simp [f]
          · intro x _ y _ h
            simp [f] at h
            exact Fin.eq_of_val_eq h
        _ ≤ ∑ i ∈ Finset.Icc (0 : ℤ) k.natAbs, (1 / 2 : ℝ) ^ i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx ⊢
            simp [hx.1.1]
            trans k
            · exact hx.2
            · exact le_abs_self k
          · intro _ _ _
            apply zpow_nonneg
            simp
        _ < _ := by exact hgeom
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), α * (2 : ℝ) ^ (i.val - τ) := by
        apply Finset.sum_le_sum
        intro i _
        apply le_of_le_of_eq (le_min_iff.mp (@hxt_le_τ i)).2
        rw [rpow_sub (by simp), rpow_sub (by simp)]
        field_simp
      _ = α * 2 ^ (k - τ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), (2 : ℝ) ^ (i.val - k) := by
        rw [Finset.mul_sum]
        congr
        ext i
        rw [mul_assoc α, ←rpow_intCast, ←rpow_add (by simp)]
        simp
      _ < α * 2 ^ (k - τ) * 2 := by rel [this]
      _ = _ := by ring
  have hgek {k : ℤ} : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≥ k), x i < 2 * α * 2 ^ (τ - k) := by
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≥ k), (2 : ℝ) ^ (k - i.val) < 2 := by
      calc
        _ = ∑ i ∈ Finset.Icc (max 0 (-k)) (n - 1 - k), (1 / 2 : ℝ) ^ i := by
          let f (i : Fin n) : ℤ := i.val - k
          have : (Finset.univ.filter (fun i : Fin n => i.val ≥ k)).image f = Finset.Icc (max 0 (-k)) (n - 1 - k) := by
            ext i
            simp [f]
            constructor <;> intro h
            · obtain ⟨j, h1, h2⟩ := h
              simp [←h2, h1]
              apply Int.le_sub_one_of_lt
              norm_cast
              exact j.2
            · let a := k + i
              have : a ≥ 0 := by
                simp [a]
                calc
                  0 ≤ k + (-k) := by simp
                  _ ≤ k + i := by rel [h.1.2]
              have ha : a.natAbs < (n : ℤ) := by
                simp [Int.natAbs_of_nonneg this, a]
                calc
                  k + i ≤ k + (n - 1 - k) := by rel [h.2]
                  _ = n - 1 := by ring
                  _ < n := by simp
              norm_cast at ha
              use ⟨a.natAbs, ha⟩
              constructor
              · simp [Int.natAbs_of_nonneg this, a, h.1.1]
              · simp [Int.natAbs_of_nonneg this, a]
          rw [←this, Finset.sum_image]
          · simp [f]
          · intro x _ y _ h
            simp [f] at h
            exact Fin.eq_of_val_eq h
        _ ≤ ∑ i ∈ Finset.Icc (0 : ℤ) (n + k.natAbs), (1 / 2 : ℝ) ^ i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx ⊢
            simp [hx.1.1]
            trans n - 1 - k
            · exact hx.2
            · calc
                _ ≤ n - k := by simp
                _ ≤ _ := by
                  rw [sub_eq_add_neg]
                  simp
                  exact neg_le_abs k
          · intro _ _ _
            apply zpow_nonneg
            simp
        _ < _ := by exact hgeom
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≥ k), α * (2 : ℝ) ^ (τ - i.val) := by
        apply Finset.sum_le_sum
        intro i _
        apply le_of_le_of_eq (le_min_iff.mp (@hxt_le_τ i)).1
        rw [rpow_sub (by simp), rpow_sub (by simp)]
        field_simp
      _ = α * 2 ^ (τ - k) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≥ k), (2 : ℝ) ^ (k - i.val) := by
        rw [Finset.mul_sum]
        congr
        ext i
        rw [mul_assoc α, ←rpow_intCast, ←rpow_add (by simp)]
        simp
      _ < α * 2 ^ (τ - k) * 2 := by rel [this]
      _ = _ := by ring
  -- \leqslant \sum_{k \geqslant 0} \alpha 2^{-w-k}+\sum_{k \geqslant 0} \alpha 2 w-1-k=f(1-w) \alpha \leqslant 3 \alpha, $$
  have hseq : s < α * 3 := by
    calc
      s = ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ ⌊τ⌋), x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ ⌊τ⌋ + 1), x i := hseq
      _ < 2 * α * 2 ^ (⌊τ⌋ - τ) + 2 * α * 2 ^ (τ - (⌊τ⌋ + 1 : ℤ)) := by rel [hlek (k := ⌊τ⌋), hgek (k := ⌊τ⌋ + 1)]
      _ = α * 2 ^ (1 - w) + α * 2 ^ w := by
        simp only [w]
        rw [rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp), rpow_sub (by simp), Int.cast_add, rpow_add (by simp)]
        field_simp
        ring
      _ = α * f w := by simp [f]; ring
      _ ≤ α * 3 := by rel [hf]
  have hαge1 : α > 1 := by
    apply lt_of_le_of_lt hsum at hseq
    nth_rw 1 [←one_mul (3 : ℝ)] at hseq
    apply mul_lt_mul_iff_of_pos_right ?_ |>.mp hseq
    simp
  -- which shows that $\log _{2}(\alpha) \geqslant 0$.
  have hlog : logb 2 α > 0 := by apply logb_pos; simp; exact hαge1

  -- We then set $\mu=\left\lfloor\tau-\log _{2}(\alpha)\right\rfloor$ and $\nu=\left\lceil\tau+\log _{2}(\alpha)\right\rceil$,
  let μ := ⌊τ - logb 2 α⌋
  let ν := ⌈τ + logb 2 α⌉
  have hμ : μ < ν := by
    simp [μ, ν]
    refine Int.floor_lt_ceil_of_lt ?_
    trans τ
    all_goals (simp; exact hlog)

  -- and $y=\tau-\log _{2}(\alpha)-\mu$, and finally $z=\nu-\tau-\log _{2}(\alpha)$,
  let y := (τ - logb 2 α) - μ
  let z := ν - (τ + logb 2 α)
  -- so that $\mu \leqslant \nu, 0 \leqslant y \leqslant 1$ and $0 \leqslant z \leqslant 1$.
  have hynonneg : 0 ≤ y := by simp [y, μ]
  have hyle1 : y ≤ 1 := by simp [y, μ]; apply le_of_lt; exact Int.fract_lt_one (τ - logb 2 α)
  have hznonneg : 0 ≤ z := by simp [z]; exact Int.le_ceil (τ + logb 2 α)
  have hzle1 : z ≤ 1 := by simp [z, ν]; apply le_of_lt; nth_rw 2 [add_comm]; apply Int.ceil_lt_add_one
  -- This time, it is the function $g: x \mapsto 2^{1-x}+x$ that is convex and satisfies $g(0)=g(1)=2$.
  let g (x : ℝ) := 2 ^ (1 - x) + x
  have hg {x : ℝ} (h1 : x ≥ 0) (h2 : x ≤ 1) : g x ≤ 2 := by
    have : 2 = g 0 ⊔ g 1 := by simp [g]; norm_num
    rw [this]
    apply ConvexOn.le_max_of_mem_Icc (s := Set.Icc 0 1)
    · apply ConvexOn.add
      · have : deriv (fun x : ℝ ↦ 2 ^ (1 - x)) = fun x => - (2 : ℝ) ^ (1 - x) * log 2 := by
          ext x
          have : (fun x : ℝ ↦ 2 ^ (1 - x)) = fun x => rexp ((1 - x) * log 2) := by
            ext x
            rw [mul_comm, exp_mul, exp_log (by simp)]
          simp [this]
          rw [_root_.deriv_exp, deriv_mul]
          rw [deriv_sub, deriv_const, deriv_const]
          simp
          left
          rw [mul_comm]
          rw [exp_mul, exp_log (by simp)]
          · exact differentiableAt_const 1
          · exact differentiableAt_id'
          · apply DifferentiableAt.sub
            · exact differentiableAt_const 1
            · exact differentiableAt_id'
          · exact differentiableAt_const _
          · apply DifferentiableAt.mul
            · apply DifferentiableAt.sub
              · exact differentiableAt_const 1
              · exact differentiableAt_id'
            · exact differentiableAt_const _
        apply convexOn_of_deriv2_nonneg'
        · exact convex_Icc 0 1
        · apply DifferentiableOn.rpow
          · exact differentiableOn_const 2
          · apply DifferentiableOn.sub
            · exact differentiableOn_const 1
            · exact differentiableOn_id'
          · simp
        · rw [this]
          apply DifferentiableOn.mul_const
          apply DifferentiableOn.neg
          apply DifferentiableOn.rpow
          · exact differentiableOn_const 2
          · apply DifferentiableOn.sub
            · exact differentiableOn_const 1
            · exact differentiableOn_id'
          · simp
        · simp [this]
          intro x _ _
          apply mul_nonneg
          · apply mul_nonneg
            · apply rpow_nonneg (by simp)
            · apply log_nonneg (by simp)
          · apply log_nonneg (by simp)
      · apply convexOn_id
        exact convex_Icc 0 1
    · simp
    · simp
    · simp
      exact ⟨h1, h2⟩
  -- We conclude that
  have hseq : s = ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ μ), x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ μ + 1 ∧ i.val < ν), x i
       + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ ν), x i := by
    simp [s]
    rw [←Finset.sum_union, ←Finset.sum_union]
    · congr
      ext i
      simp
      by_cases h : i.val ≤ μ
      · simp [h]
      · by_cases h2 : i.val < ν
        · simp [h2]
          simp at h
          have : μ + 1 ≤ ↑↑i := by exact h
          simp [this]
        · simp at h2
          simp [h2]
    · simp
      constructor <;> (apply Finset.disjoint_filter.mpr; intro x _ hx; simp)
      · exact lt_of_le_of_lt hx hμ
      · exact hx.2
    · apply Finset.disjoint_filter.mpr
      intro x _ hx
      have : ¬ μ + 1 ≤ x.val := by simp; exact Int.lt_add_one_iff.mpr hx
      simp [this]
  have hle2 : ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ μ + 1 ∧ i.val < ν), x i ≤ 2 * logb 2 α + y + z - 1 := by
    trans ∑ _ ∈ Finset.univ.filter (fun i : Fin n => i.val ≥ μ + 1 ∧ i.val < ν), 1
    · apply Finset.sum_le_sum
      intro i _
      exact hxt_le_one
    · simp
      trans ν - μ - 1
      · let t := Finset.Ico (μ + 1) ν
        have ht : (t.card : ℝ) = ν - μ - 1 := by norm_cast; simp [t]; rw [tsub_tsub ν μ 1]; simp; exact hμ
        rw [←ht]
        norm_cast
        let f (i : Fin n) : ℤ := i.val
        apply Finset.card_le_card_of_injOn f
        · intro i hi
          simp at hi
          simp [f, t]
          exact hi
        · intro i _ j _ h
          simp [f] at h
          exact Fin.eq_of_val_eq h
      · simp [μ, ν]
        apply le_of_eq
        simp [y, z]
        ring
  -- $$ \begin{aligned} s & \leqslant \sum_{t \leqslant \mu} x_{t}+\left(x_{\mu+1}+\cdots+x_{\nu-1}\right)+\sum_{t \geqslant \nu} x_{t} \ & 2^{s-3}. \end{aligned} $$
  have hsle : s < 2 * logb 2 α + 3 := by
    calc
      s = ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ μ), x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ μ + 1 ∧ i.val < ν), x i
          + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ ν), x i := hseq
      _ < 2 * α * 2 ^ (μ - τ) + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ μ + 1 ∧ i.val < ν), x i + 2 * α * 2 ^ (τ - ν) := by rel [hlek, hgek]
      _ ≤ 2 * α * 2 ^ (μ - τ) + (2 * logb 2 α + y + z - 1) + 2 * α * 2 ^ (τ - ν) := by rel [hle2]
      _ = 2 * α * 2 ^ (-logb 2 α - y) + (2 * logb 2 α + y + z - 1) + 2 * α * 2 ^ (-logb 2 α - z) := by
        congr 1
        · simp; left
          congr 1
          simp only [μ, y]
          ring
        · simp; left
          congr 1
          simp [ν, z]
          ring
      _ = 2 * 2 ^ (-y) + (2 * logb 2 α + y + z - 1) + 2 * 2 ^ (-z) := by
        congr 1
        · simp
          rw [rpow_sub (by simp), rpow_neg (by simp), rpow_logb (by simp) (by simp) hαpos, rpow_neg (by simp)]
          field_simp
          ring
        · rw [rpow_sub (by simp), rpow_neg (by simp), rpow_logb (by simp) (by simp) hαpos, rpow_neg (by simp)]
          field_simp
          ring
      _ = (2 ^ (1 - y) + y) + (2 ^ (1 - z) + z) + (2 * logb 2 α - 1) := by
        rw [rpow_sub (by simp), rpow_sub (by simp) 1 z, rpow_neg (by simp), rpow_neg (by simp)]
        simp
        field_simp
        ring
      _ ≤ 2 + 2 + (2 * logb 2 α - 1) := by rel [hg hynonneg hyle1, hg hznonneg hzle1]
      _ = _ := by ring
  exact sub_right_lt_of_lt_add hsle