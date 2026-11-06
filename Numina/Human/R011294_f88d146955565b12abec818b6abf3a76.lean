import Mathlib

open Function

/-Let $f: \mathbb{N} \rightarrow \mathbb{N}$ be a function, and let $f^{m}$ be $f$ applied $m$ times. Suppose that for every $n \in \mathbb{N}$ there exists a $k \in \mathbb{N}$ such that $f^{2 k}(n)=n+k$, and let $k_{n}$ be the smallest such $k$. Prove that the sequence $k_{1}, k_{2}, \ldots$ is unbounded.-/
theorem algebra_24155 {f k : ℕ → ℕ} (fge1 : ∀ n, 1 ≤ f n)
(hk : ∀ m, IsLeast {l | f^[2*l] m = m + l ∧ 1 ≤ l} (k m)) : ¬ BddAbove (k '' Set.Ici 1):= by
-- Rewrite our assumptions
  simp [IsLeast, lowerBounds] at hk
  rw [forall_and] at hk; rcases hk with ⟨hk1, hk2⟩
  rw [forall_and] at hk1; rcases hk1 with ⟨hk1, kge1⟩
  suffices : ¬ BddAbove (k '' Set.univ)
  · simp [not_bddAbove_iff] at *; intro x; by_cases h : k 0 ≤ x
    · obtain ⟨y, hy⟩ := this x; use y; constructor
      · by_contra!; simp at this; rw [this] at hy; linarith
      exact hy
    obtain ⟨y, hy⟩ := this (x ⊔ k 0); use y; have : k 0 ≤ x ⊔ k 0 := by apply Nat.le_max_right
    have : x ≤ x ⊔ k 0 := by apply Nat.le_max_left
    constructor; by_contra!; simp at this; rw [this] at hy; all_goals linarith
-- Restrict our attention to the following set
  let S := {m | ∃ n, f^[n] 1 = m}
-- Denote the function of iterating $f$ at $1$ by itf1
  let itf1 : ℕ → ℕ := fun t => f^[t] 1
-- Prove that $f$ maps $S$ to $S$
  have fmapsto : Set.MapsTo f S S := by
    rw [Set.mapsTo', Set.subset_def]; simp [S]
    intro i; use i+1
    rw [add_comm, iterate_add_apply, iterate_one]
-- Prove that $S$ is unbounded by induction
  have unbdS : ¬ BddAbove S := by
    rw [not_bddAbove_iff]; intro a; simp [S]
    induction a with
    | zero => use (2 * k 1); rw [hk1]; linarith
    | succ a ih =>
      rcases ih with ⟨t, ht⟩; replace ht : a + 1 ≤ f^[t] 1 := by linarith
      use (2 * k (f^[t] 1) + t); rw [iterate_add_apply, hk1]
      have := kge1 (f^[t] 1); linarith
-- Prove that $S$ does not contain any periodic point of $f$, because if so $S$ would be finite, in particular bounded, contradicting to the fact that $S$ is unbounded
  have noperiS : ∀ y ∈ S, y ∉ periodicPts f := by
    intro y yS yperi; simp [S, mem_periodicPts] at yS yperi
    rcases yS with ⟨m, hm⟩; rcases yperi with ⟨n, ⟨npos,peri⟩⟩
    suffices : S.Finite
    · rw [Set.finite_iff_bddAbove] at this; contradiction
  -- Prove the difference set $S\itf1(Finset.range m)$ is contained in the set of periodic orbit of $f$ at $y$
    have : (S \ itf1 '' Finset.range m) ⊆ (periodicOrbit f y).toFinset := by
      rw [Set.subset_def]; simp [S, periodicOrbit]; by_contra h'; push_neg at h'
      rcases h' with ⟨x, ⟨h1, h2⟩⟩; simp [itf1] at h1
      replace h1 : m ≤ x := by
        by_contra h'; push_neg at h'
        have := h1 x h'; contradiction
      specialize h2 ((x - m) % (minimalPeriod f y))
      replace h2 : f^[x] 1 ≠ f^[(x - m) % minimalPeriod f y] y := by
        apply h2 ; apply Nat.mod_lt; rw [gt_iff_lt]
        rw [minimalPeriod_pos_iff_mem_periodicPts, mem_periodicPts]; use n
      rw [Function.iterate_mod_minimalPeriod_eq] at h2
      nth_rw 1 [show x = x - m + m by rw [Nat.sub_add_cancel]; assumption] at h2
      rw [iterate_add_apply, hm] at h2; contradiction
    suffices : (S \ itf1 '' Finset.range m).Finite
    · apply Set.Finite.of_diff this; apply Finite.Set.finite_image
    apply Finite.Set.subset _ this
-- Prove that the function of iterating $f$ at $1$ is injective
  have inj_itf1 : Injective itf1 := by
    intro a b hab; simp [itf1] at hab
    by_contra aneb; push_neg at aneb; rw [Nat.ne_iff_lt_or_gt] at aneb
    rcases aneb with h|h
  -- If $a$ is less than $b$, prove that $f^[a] 1$ is a periodic point of $f$, contradicting to the fact that $S$ does not contain any periodic point of $f$
    · have peri_a : (f^[a] 1) ∈ periodicPts f := by
        rw [mem_periodicPts]; use b-a
        rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply]
        rw [Nat.sub_add_cancel, ← hab]; constructor
        · rw [gt_iff_lt, Nat.sub_pos_iff_lt]; assumption
        ring_nf; linarith
      specialize noperiS (f^[a] 1)
      replace noperiS : f^[a] 1 ∉ periodicPts f := by
        apply noperiS; simp only [S, Set.mem_setOf_eq]; use a
      contradiction
  -- If $a$ is greater than $b$, prove that $f^[b] 1$ is a periodic point of $f$, contradicting to the fact that $S$ does not contain any periodic point of $f$
    have peri_b : (f^[b] 1) ∈ periodicPts f := by
      rw [mem_periodicPts]; use a-b
      rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply]
      rw [Nat.sub_add_cancel, hab]; constructor
      · rw [gt_iff_lt, Nat.sub_pos_iff_lt]; assumption
      ring_nf; linarith
    specialize noperiS (f^[b] 1)
    replace noperiS : f^[b] 1 ∉ periodicPts f := by
      apply noperiS; simp only [S, Set.mem_setOf_eq]; use b
    contradiction
-- Prove that $f$ is injective on $S$ by applying the injectivity of itf1
  have injf : Set.InjOn f S := by
    rw [Set.InjOn]; simp [S]; intro a b hab
    nth_rw 1 3 [← iterate_one f] at hab; repeat rw [← iterate_add_apply] at hab
    congr; rw [← @Nat.add_left_cancel_iff _ _ 1]; apply inj_itf1; assumption
-- Prove that funtion of iterating $f$ $n$-times is injective on $S$
  have injitf : ∀ n, Set.InjOn f^[n] S := by apply Set.InjOn.iterate; any_goals assumption
-- Define a new function $g$ to be the function iterating $f$ $2*k_t$ times
  let g (t : ℕ) : ℕ := f^[2 * k t] t
-- Prove that applying $g$ to any number $t$ is the same as shifting $t$ by $k_t$
  have hg : ∀ t, g t = t + k t := by intro t; simp [g]; apply hk1
-- Prove that the function of iterating $g$ at any number $t$ in $S$, equals iterating $f$ some times at $1$ by induction
  have itg_itf : ∀ n t, t ∈ S → ∃ m , g^[n] t = f^[m] 1 := by
    intro n t ht; simp [S] at ht; rcases ht with ⟨w, hw⟩
    induction n with
    | zero => use w; simp; symm; assumption
    | succ n ih =>
      rcases ih with ⟨z, hz⟩; use 2*k (f^[z] 1)+z
      rw [add_comm, iterate_add_apply, iterate_one, hz]
      simp [g]; rw [← iterate_add_apply]
-- Prove the following auxillary lemma for computational use later
  have aux : ∀ w m n, g^[w] (f^[n] 1) = f^[m] 1 → m + 2 * f^[n] 1 = n + 2 * f^[m] 1 := by
    intro w; induction w with
    | zero =>
      intro m n hmn; rw [iterate_zero] at hmn; simp at hmn
      apply inj_itf1 at hmn; rw [hmn]
    | succ w ih =>
      intro m n hmn; rw [iterate_add_apply, iterate_one] at hmn
      rw [show g (f^[n] 1)=f^[2*k (f^[n] 1)] (f^[n] 1) by simp [g]] at hmn
      rw [← iterate_add_apply] at hmn; apply ih at hmn
      rw [iterate_add_apply, hk1, mul_add, ← add_assoc, add_comm] at hmn
      rw [add_assoc, Nat.add_left_cancel_iff] at hmn; assumption
-- Prove that $g$ maps $S$ to $S$
  have gmapsto : Set.MapsTo g S S := by
    rw [Set.mapsTo', Set.subset_def]; simp [S, g]
    intro i; use i+2*k (f^[i] 1)
    rw [add_comm, iterate_add_apply]
-- Prove that $g$ is injective on $S$ by contradiction
  have injg : Set.InjOn g S := by
    rw [Set.InjOn]; simp [S]; intro a b hab; let h'ab := hab
    simp [hg] at h'ab; simp [g] at hab
    repeat rw [← iterate_add_apply] at hab
    by_contra h; push_neg at h
    rw [Nat.ne_iff_lt_or_gt] at h; rcases h with h|h
  -- If $f^[a] 1$ is less than $f^[b] 1$, apply the minimality of $k_(f^[a] 1)$ and the injectivity of the iterating function of $f$ to derive a contradiction
    · apply_fun (fun t => t - f^[a] 1) at h'ab
      rw [Nat.add_sub_cancel_left, Nat.sub_add_comm] at h'ab
      apply_fun (fun t => t - k (f^[b] 1)) at h'ab
      rw [Nat.add_sub_cancel] at h'ab
      suffices : k (f^[a] 1) ≤ k (f^[a] 1) - k (f^[b] 1)
      · have := kge1 (f^[a] 1)
        have := kge1 (f^[b] 1)
        have : k (f^[a] 1) - k (f^[b] 1) < k (f^[a] 1) := by apply Nat.sub_lt; any_goals linarith
        linarith
      apply hk2; nth_rw 2 [h'ab]; rw [Nat.add_sub_cancel', ← iterate_add_apply]
      have : 2 * k (f^[a] 1) + a = 2 * k (f^[b] 1) + (2 * (k (f^[a] 1) - k (f^[b] 1)) + a) := by
        rw [Nat.mul_sub, ← Nat.add_assoc, Nat.add_sub_cancel']
        apply Nat.mul_le_mul; linarith
        apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt, h'ab]
        rw [Nat.sub_pos_iff_lt]; assumption
      rw [this, iterate_add_apply] at hab
      nth_rw 2 [iterate_add_apply] at hab; apply injitf (2 * k (f^[b] 1)) at hab
      assumption; any_goals simp [S]
      linarith; rw [h'ab, Nat.le_sub_iff_add_le]; any_goals linarith
  -- If $f^[b] 1$ is less than $f^[a] 1$, apply the minimality of $k_(f^[b] 1)$ and the injectivity of the iterating function of $f$ to derive a contradiction
    apply_fun (fun t => t - f^[b] 1) at h'ab
    rw [Nat.add_sub_cancel_left, Nat.sub_add_comm] at h'ab
    apply_fun (fun t => t - k (f^[a] 1)) at h'ab
    rw [Nat.add_sub_cancel] at h'ab
    suffices : k (f^[b] 1) ≤ k (f^[b] 1) - k (f^[a] 1)
    · have := kge1 (f^[a] 1)
      have := kge1 (f^[b] 1)
      have : k (f^[b] 1) - k (f^[a] 1) < k (f^[b] 1) := by apply Nat.sub_lt; any_goals linarith
      linarith
    apply hk2; nth_rw 2 [← h'ab]; rw [Nat.add_sub_cancel', ← iterate_add_apply]
    have : 2 * k (f^[b] 1) + b = 2 * k (f^[a] 1) + (2 * (k (f^[b] 1) - k (f^[a] 1)) + b) := by
      rw [Nat.mul_sub, ← Nat.add_assoc, Nat.add_sub_cancel']
      apply Nat.mul_le_mul; linarith
      apply Nat.le_of_lt; rw [← Nat.sub_pos_iff_lt, ← h'ab]
      rw [Nat.sub_pos_iff_lt]; assumption
    rw [this, iterate_add_apply] at hab
    nth_rw 1 [iterate_add_apply] at hab; apply injitf (2 * k (f^[a] 1)) at hab
    symm; assumption; any_goals simp [S]
    linarith; rw [← h'ab, Nat.le_sub_iff_add_le]; any_goals linarith
-- Prove that the function of iterating $g$ is injective on $S$
  have injitg : ∀ n, Set.InjOn g^[n] S := by apply Set.InjOn.iterate; any_goals assumption
-- let $T$ to be the difference set of $S$ and $g(S)$, prove that $T$ is nonempty by showing $1$ belongs to $T$
  let T := S \ g '' S
  have oneinT : 1 ∈ T := by
    simp [T, S, hg]; constructor; use 0; norm_num
    intro i hi; have := kge1 (f^[i] 1)
    suffices : f^[i] 1 = 1; linarith
    rw [Nat.eq_iff_le_and_ge]; constructor; linarith
    by_cases h : i < 1; simp at h; rw [h, iterate_zero]; norm_num
    push_neg at h; rw [show i=i-1+1 by rw [Nat.sub_add_cancel]; linarith]
    rw [add_comm, iterate_add_apply, iterate_one]; apply fge1
  have nonempT : T.Nonempty := by use 1
-- Define for any number $t$ the set of numbers obtained by iterating $g$ at $t$ by $C_t$
  let C (t : ℕ) : Set ℕ := {m | ∃ l, g^[l] t = m}
-- Prove that for any different numbers $i$ and $j$ in $T$, $C_i$ and $C_j$ are disjoint
  have disjc : ∀ i j, i ≠ j → i ∈ T → j ∈ T → C i ∩ C j = ∅ := by
    intro i j inej hi hj; simp [T, S] at hi hj
    rcases hi with ⟨⟨l, hi1⟩, hi2⟩; rcases hj with ⟨⟨m, hj1⟩, hj2⟩
    ext x; simp [C]; intro p hp q hq; rw [← hp] at hq
  -- Exclude the case when $p=q$, because we can apply the injectivity of the function of iterating $g$ to prove that $i$ equals $j$, which is a contradiction
    by_cases pneq : p = q
    · rw [pneq] at hq; apply injitg q at hq; symm at hq; contradiction
      any_goals simp [S]
      use m; use l
    push_neg at pneq; rw [Nat.ne_iff_lt_or_gt] at pneq
    cases pneq
  -- If $p$ is less than $q$, rewriting $i$ as $g(f^[w] 1)$ shows it belongs to $g(S)$, contradicting to the definition of the set $T$
    · have : q - p = 1 + (q - p - 1) := by
        rw [Nat.add_sub_cancel']; suffices: 0 < q - p; linarith
        rw [Nat.sub_pos_iff_lt]; assumption
      rcases itg_itf (q-p-1) j (show _ by simp [S]; use m) with ⟨w, hw⟩
      rw [show q=q-p+p by rw [Nat.sub_add_cancel];linarith] at hq
      rw [add_comm, iterate_add_apply] at hq; apply injitg p at hq
      rw [this, iterate_add_apply, iterate_one] at hq
      rw [hw] at hq; have := hi2 w; contradiction
      rw [this, iterate_add_apply, iterate_one]; apply gmapsto
      simp [S]; use w; symm; assumption
      simp [S]; use l
  -- If $q$ is less than $p$, rewriting $j$ as $g(f^[w] 1)$ shows it belongs to $g(S)$, contradicting to the definition of the set $T$
    have : p - q = 1 + (p - q - 1) := by
      rw [Nat.add_sub_cancel']; suffices: 0 < p - q; linarith
      rw [Nat.sub_pos_iff_lt]; assumption
    rcases itg_itf (p-q-1) i (show _ by simp [S]; use l) with ⟨w, hw⟩
    rw [show p=p-q+q by rw [Nat.sub_add_cancel];linarith] at hq
    rw [add_comm, iterate_add_apply] at hq; apply injitg q at hq
    rw [this, iterate_add_apply, iterate_one] at hq
    rw [hw] at hq; symm at hq; have := hj2 w; contradiction
    simp [S]; use m
    rw [this, iterate_add_apply, iterate_one]; apply gmapsto
    simp [S]; use w; symm; assumption
-- Prove that the union $C_i$ for all $i$ in $T$ is the whole set $S$
  have unionC : S = ⋃ i ∈ T, C i := by
    ext x; simp [T, S, C]; constructor
  -- Prove $S$ is contained in the union on RHS by using strong induction and split to two cases
    · induction x using Nat.strong_induction_on
      rename_i hn; rename_i n
      rintro ⟨n', hn'⟩; by_cases h' : ∃ a, g (f^[a] 1) = f^[n'] 1
      · rcases h' with ⟨w, hw⟩
        have : (f^[w] 1) < n := by
          rw [hg] at hw; have := kge1 (f^[w] 1)
          linarith
        have : ∃ i, ((∃ n, f^[n] 1 = i) ∧ ∀ (x : ℕ), ¬g (f^[x] 1) = i) ∧ ∃ l, g^[l] i = f^[w] 1 := by
          apply hn; assumption; use w
        rcases this with ⟨p, ⟨⟨⟨q, hq⟩,hp2⟩,⟨r,hr⟩⟩⟩
        use p; constructor; constructor; use q; assumption
        nth_rewrite 1 [← iterate_one g] at hw
        rw [← hr, ← iterate_add_apply] at hw
        use 1+r; linarith
      push_neg at h'; use f^[n'] 1; constructor; constructor
      use n'; push_neg; assumption; use 0
      rw [iterate_zero]; assumption
  -- Prove the reversed inclusion by rewriting the assumptions and applying itg_itf
    rintro ⟨p, ⟨⟨⟨q,hq⟩,hp2⟩,⟨r,hr⟩⟩⟩; rw [← hq] at hr
    rcases itg_itf r (f^[q] 1) (show _ by use q) with ⟨w, hw⟩
    use w; linarith
-- Prove that $T$ is infinite by assuming it is finite and derive a contradiction
  have infiT : Set.Infinite T := by
    by_contra h; rw [Set.not_infinite] at h
    have : Fintype T := by exact h.fintype
    let t := T.toFinset.max' (show _ by simp; assumption)
    have tge1 : 1 ≤ t := by apply Finset.le_max'; simp; assumption
    have Tlet : ∀ x ∈ T, x ≤ t := by intro x hx; apply Finset.le_max'; simp; assumption
    suffices : Finset.image itf1 (Finset.range (4 * t + 1)) ⊆ Finset.range (3 * t + 1)
    · apply Finset.card_le_card at this; rw [Finset.card_image_of_injective] at this
      norm_num at this; linarith; assumption
    rw [Finset.subset_iff]; simp; intro n hn; simp [itf1]
    have : f^[n] 1 ∈ S := by simp [S]
    rw [unionC] at this; simp at this; rcases this with ⟨t',⟨ht'1,ht'2⟩⟩
    let h't'1 := ht'1; simp [C] at ht'2; rcases ht'2 with ⟨w, hw⟩
    simp [T, S] at h't'1; rcases h't'1 with ⟨⟨u,hu⟩,h't'1⟩
    rw [← hu] at hw; apply aux at hw; apply Tlet at ht'1; linarith
-- Prove our main goal by contradiction, assume the set in question is bounded above by some number $a$
  intro bd; rw [bddAbove_def] at bd; rcases bd with ⟨a, bda⟩; simp at bda
-- Since $T$ is infinite, we can choose $a+1$ different elements from it
  have : ∃ f : ℕ → ℕ, (Finset.range (a + 1)).toSet ⊆ f ⁻¹' T ∧ Set.InjOn f (Finset.range (a + 1)).toSet := by
    apply Set.Finite.exists_injOn_of_encard_le; apply Finset.finite_toSet
    nth_rw 2 [Set.encard_eq_top]; simp; assumption
  rcases this with ⟨u, ⟨hu1, hu2⟩⟩; simp [Set.subset_def] at hu1
-- Denote the maximum of the $a+1$ elements by $M$
  let M := (u '' Finset.range (a + 1)).toFinset.max' (show _ by use u 0; simp; use 0; simp)
  have maxM : ∀ i ∈ Finset.range (a + 1), u i ≤ M := by
    intro i hi; simp at hi; apply Finset.le_max'
    simp; use i
-- Prove the following key lemma about this maximum $M$
  have : ∀ i ∈ Finset.range (a + 1), ∃ j, g^[j] (u i) ∈ Finset.Icc (M + 1) (M + a) := by
    intro i hi; simp at hi
  -- Prove by contradiction
    by_contra h'; push_neg at h'; simp at h'
  -- Denote the function of iterating $g$ at $u_i$ by itgui and prove it is strictly increasing by induction
    let itgui : ℕ → ℕ := fun t => g^[t] (u i)
    have smono_itgui : StrictMono itgui := by
      intro p q; induction q with
      | zero => simp
      | succ q ih =>
        by_cases h : p < q
        · replace ih := ih h; intro; simp only [itgui]
          rw [add_comm, iterate_add_apply, iterate_one, hg]
          have := kge1 (g^[q] (u i)); linarith
        push_neg at h; intro h1; replace h1 : p = q := by linarith
        rw [h1]; simp only [itgui]
        rw [add_comm, iterate_add_apply, iterate_one, hg]
        have := kge1 (g^[q] (u i)); linarith
  -- Denote the set of numbers $j$ such that $g^[j] (u_i)$ is less than $M+1$ by bdM
  -- and prove it is nonempty by showing $0$ belongs to bdM
    let bdM := {j | g^[j] (u i) < M + 1}
    have nonempbdM : bdM.Nonempty := by
      use 0; simp [bdM]; suffices : u i ≤ M; linarith
      apply maxM; simp; assumption
    have finbdM : Fintype bdM := by
      suffices : bdM.Finite; exact this.fintype
      have r1 : bdM = itgui ⁻¹' (Finset.range (M + 1)) := by ext x; simp [bdM, itgui]
      apply_fun (fun t => itgui '' t) at r1
      have := Set.image_preimage_subset itgui (Finset.range (M + 1))
      rw [← r1] at this; apply Finite.Set.subset at this
      apply Finite.Set.finite_of_finite_image at this; exact this
      apply Set.injOn_of_injective; apply StrictMono.injective; assumption
    let l := bdM.toFinset.max' (show _ by simp; assumption)
    have maxl : ∀ n ∈ bdM, n ≤ l := by
      intros; apply Finset.le_max'; rw [Set.mem_toFinset]; assumption
    have hl : l ∈ bdM := by simp only [l]; rw [← Set.mem_toFinset]; apply Finset.max'_mem
    simp [bdM] at hl; suffices : M + 1 ≤ g^[1+l] (u i)
    · apply h' at this; rw [iterate_add_apply, iterate_one, hg] at this
      have := bda (g^[l] (u i)); linarith
    suffices : 1 + l ∉ bdM; simp [bdM] at this; assumption
    intro h; apply maxl at h; linarith
  choose v hv using this
-- Construct a new function $w$ from this lemma and apply the Pigeonhole principle on $w$
  let w : ℕ → ℕ := fun t => if ht : t ∈ Finset.range (a + 1) then g^[v t ht] (u t) else 0
  have : ∃ x ∈ Finset.range (a + 1), ∃ y ∈ Finset.range (a + 1), x ≠ y ∧ w x = w y := by
    apply @Finset.exists_ne_map_eq_of_card_lt_of_maps_to _ _ _ (Finset.Icc (M+1) (M+a))
    simp; intro m hm; simp only [w]; split_ifs; apply hv
  rcases this with ⟨x, hx, y, ⟨hy, xney, hxy⟩⟩
  simp only [w] at hxy; split_ifs at hxy
-- Prove that $C_(u x)$ and $C_(u y)$ have a nonempty intersection, which contradicts to the fact that they are disjoint by disjc
  have nempxy : ((C (u x)) ∩ (C (u y))).Nonempty := by
    use g^[v x hx] (u x); simp only [Set.mem_inter_iff]
    simp [C]; use v y hy; symm; assumption
  rw [Set.nonempty_iff_ne_empty] at nempxy
  have empxy : (C (u x)) ∩ (C (u y)) = ∅ := by
    simp at hx hy; apply disjc; rw [Set.InjOn.ne_iff]
    assumption; exact hu2; simp
    any_goals assumption
    any_goals apply hu1; assumption
  contradiction