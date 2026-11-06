import Mathlib

open Finset

/- Find the positive integer $n\,$ for which\[\lfloor\log_2{1}\rfloor+\lfloor\log_2{2}\rfloor+\lfloor\log_2{3}\rfloor+\cdots+\lfloor\log_2{n}\rfloor=1994\](For real $x\,$, $\lfloor x\rfloor\,$ is the greatest integer $\le x.\,$) -/
theorem number_theory_706 (n: ℕ): ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i = 1994 ↔ n = 312 := by
  have p (n: ℕ) (n_gt_zero: n > 0) :
    ∑ x ∈ range (Nat.log 2 n), 2 ^ x * x
      + (n + 1 - 2 ^ Nat.log 2 n) * Nat.log 2 n
      = ∑ x ∈ range (n + 1) \ {0}, Nat.log 2 x := by
    have p := Finset.sum_fiberwise_of_maps_to' (s := range (n + 1) \ {0}) (t := range (Nat.log 2 n + 1)) (g := Nat.log 2) (f := id)
      (h := by
        intro i p
        rw [mem_sdiff, mem_range] at *

        apply Nat.lt_add_one_of_le
        apply Nat.log_monotone
        exact Nat.le_of_lt_add_one p.1
      )

    simp at p
    rw [<- p]
    clear p
    rw [Finset.sum_range_succ]


    /- Note that if $2^x \le a<2^{x+1}$ for some $x\in\mathbb{Z}$, then $\lfloor\log_2{a}\rfloor=\log_2{2^{x}}=x$.
  Thus, there are $2^{x+1}-2^{x}=2^{x}$ integers $a$ such that $\lfloor\log_2{a}\rfloor=x$. So the sum of $\lfloor\log_2{a}\rfloor$ for all such $a$ is $x\cdot2^x$. -/
    have p_1 : ∑ x ∈ range (Nat.log 2 n), (filter (fun i ↦ Nat.log 2 i = x) (range (n + 1) \ {0})).card * x = ∑ x ∈ range (Nat.log 2 n), 2^x * x := by
      -- This uses the congruence lemma `Finset.sum_congr` for sums.
      congr! with x h
      simp [mem_range] at h

      have q := Finset.filter_congr
        (show ∀i ∈ range (n + 1) \ {0}, Nat.log 2 i = x ↔ 2 ^ x ≤ i ∧ i < 2 ^ (x + 1) from by
            intro i s
            simp at s
            exact Nat.log_eq_iff (Or.inr ⟨by norm_num, s.2⟩)
          )
      rw [q]

      have s : (filter (fun x_1 ↦ 2 ^ x ≤ x_1 ∧ x_1 < 2 ^ (x + 1)) (range (n + 1) \ {0})) = Finset.Ico (2^x) (2^(x+1)) := by
        apply Finset.ext
        intro i
        simp
        intro s t
        constructor
        case h.right =>
          have s' : 0 < 2^x := Nat.pos_pow_of_pos x (by norm_num)
          linarith
        case h.left =>
          apply Nat.succ_lt_succ at h
          apply Nat.le_of_lt_add_one at h
          apply Nat.pow_le_pow_of_le_right (show 2 > 0 from by norm_num) at h

          replace h: i < 2 ^ (Nat.log 2 n) := Nat.lt_of_lt_of_le t h
          have t': 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self _ (Nat.ne_of_gt n_gt_zero)
          linarith

      rw [s, Nat.card_Ico]
      symm
      apply Nat.eq_sub_of_add_eq
      ring


    /- Let $k$ be the integer such that $2^k \le n<2^{k+1}$. So for each integer $j< k$, there are $2^j$ integers $a\le n$ such that $\lfloor\log_2{a}\rfloor=j$, and there are $n-2^k+1$ such integers such that $\lfloor\log_2{a}\rfloor=k$. -/
    have p_2: filter (fun i ↦ Nat.log 2 i = Nat.log 2 n) (range (n + 1) \ {0}) = Finset.Ico (2^(Nat.log 2 n)) (n + 1) := by
      apply Finset.ext
      intro i
      simp
      constructor
      case h.mp =>
        intro ⟨⟨s1,s2⟩, s3⟩
        rw [Nat.log_eq_iff (show Nat.log 2 n ≠ 0 ∨ 1 < 2 ∧ i ≠ 0 from
          Or.inr ⟨by norm_num, s2⟩)] at s3
        exact ⟨s3.1, s1⟩
      case h.mpr =>
        intro ⟨s1,s2⟩
        have i_ne_zero : i ≠ 0 := by
          apply Nat.ne_zero_iff_zero_lt.mpr
          apply Nat.lt_of_lt_of_le _ s1
          apply Nat.pow_pos
          norm_num

        constructor
        case left => exact ⟨s2, i_ne_zero⟩
        case right =>
          rw [Nat.log_eq_iff (show Nat.log 2 n ≠ 0 ∨ 1 < 2 ∧ i ≠ 0 from
          Or.inr ⟨by norm_num, i_ne_zero⟩)]
          refine ⟨s1, ?_⟩
          apply Nat.lt_of_lt_of_le s2 ?_
          clear s1
          apply Nat.le_of_lt_succ
          apply Nat.succ_lt_succ
          apply Nat.lt_pow_succ_log_self
          norm_num

    replace p_2: (filter (fun i ↦ Nat.log 2 i = Nat.log 2 n) (range (n + 1) \ {0})).card = n + 1 - 2^(Nat.log 2 n) := by
      rw [p_2, Nat.card_Ico]

    rw [p_1, p_2]

  -- We treat the case `n = 0` separately.
  cases (Nat.eq_zero_or_pos n) with
  | inl s => rw [s]; simp
  | inr n_gt_zero =>

    /- Through computation: $\sum_{j=0}^{7}(j\cdot2^j)=1538<1994$ and $\sum_{j=0}^{8}(j\cdot2^j)=3586>1994$. Thus, $k=8$.
So, $\sum_{j=0}^{k-1}(j\cdot2^j) + k(n-2^k+1) = 1538+8(n-2^8+1)=1994 \Rightarrow n = \boxed{312}$. -/

    -- To show uniqueness of our solution, we will use that the sum we determined is strictly monotone in `n`.
    let f (n: ℕ) := ∑ i ∈ range (n + 1) \ {0}, Nat.log 2 i

    have f_inj_on : Set.InjOn f (Set.Ici 1) := by
      apply StrictMonoOn.injOn
      unfold StrictMonoOn
      intro n p m q s
      -- apply strictMono_nat_of_lt_succ
      unfold_let f
      simp
      -- This tactic is pretty useful whenever subtraction of naturals is needed
      zify
      rw [
        Finset.sum_sdiff_eq_sub (show {0} ⊆ range (n + 1) from by simp),
        Finset.sum_sdiff_eq_sub (show {0} ⊆ range (m + 1) from by simp)]

      rw [(show m + 1 = (n + 1) + (m - n) from by
        zify [s]
        ring
        )]
      rw [Finset.sum_range_add _ (n + 1) (m - n)]
      simp
      norm_cast
      apply lt_of_lt_of_le (show 0 < ∑ x ∈ range 1, ↑(Nat.log 2 (n + 1 + x)) from by simp_all)
      apply Finset.sum_mono_set
      simp [s]

    have val_312: f 312 = 1994 := by
      unfold_let f
      simp only []
      rw [<- p 312 (by norm_num)]
      simp [Nat.log, Finset.sum_range_succ]

    save
    constructor
    case inr.mp =>
      intro q
      have val_n: f n = 1994 := q
      unfold Set.InjOn at f_inj_on
      -- simp at f_inj_on
      apply (f_inj_on)
      exact n_gt_zero
      norm_num
      rw [val_n, val_312]

    case inr.mpr =>
      intro q
      rw [q]
      exact val_312