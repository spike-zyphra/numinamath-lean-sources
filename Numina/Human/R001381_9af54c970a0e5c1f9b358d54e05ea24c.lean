import Mathlib
open Finset
def op (u v : ℤ) (d : Fin 2) : ℤ := if d = 0 then 2 * u + 3 * v else 3 * u + v
def eval_pair (u v : ℤ) : List (Fin 2) → (ℤ × ℤ) :=
  let rec go (u v : ℤ) : List (Fin 2) → (ℤ × ℤ)
    | [] => (u, v)
    | d :: ds => go v (op u v d) ds
  go u v
def eval_word (u v : ℤ) (w : List (Fin 2)) : ℤ := (eval_pair u v w).2
lemma op_linearity (c₁ c₂ u₁ v₁ u₂ v₂ : ℤ) (d : Fin 2) :
    op (c₁*u₁ + c₂*u₂) (c₁*v₁ + c₂*v₂) d = c₁ * op u₁ v₁ d + c₂ * op u₂ v₂ d := by
  fin_cases d <;> simp [op] <;> ring
lemma eval_pair_linearity (c₁ c₂ u₁ v₁ u₂ v₂ : ℤ) (w : List (Fin 2)) :
    eval_pair (c₁*u₁ + c₂*u₂) (c₁*v₁ + c₂*v₂) w =
    let p₁ := eval_pair u₁ v₁ w
    let p₂ := eval_pair u₂ v₂ w
    (c₁ * p₁.1 + c₂ * p₂.1, c₁ * p₁.2 + c₂ * p₂.2) := by
  induction w generalizing u₁ v₁ u₂ v₂ with
  | nil => simp [eval_pair, eval_pair.go]
  | cons d ds ih =>
    simp [eval_pair, eval_pair.go, ih, op_linearity]
    simp_all only
    apply ih
lemma eval_word_linearity (c₁ c₂ u₁ v₁ u₂ v₂ : ℤ) (w : List (Fin 2)) :
    eval_word (c₁*u₁ + c₂*u₂) (c₁*v₁ + c₂*v₂) w =
    c₁ * eval_word u₁ v₁ w + c₂ * eval_word u₂ v₂ w := by
  dsimp [eval_word]
  rw [eval_pair_linearity]
lemma op_2_1_is_7 (d : Fin 2) : op 2 1 d = 7 := by
  fin_cases d <;> simp [op]
lemma eval_word_2_1_cons (d : Fin 2) (ds : List (Fin 2)) :
    eval_word 2 1 (d :: ds) = eval_word 1 7 ds := by
  simp [eval_word, eval_pair, eval_pair.go, op_2_1_is_7]
lemma eval_pair_append_singleton (u v : ℤ) (w : List (Fin 2)) (d : Fin 2) :
    eval_pair u v (w ++ [d]) = let p := eval_pair u v w; (p.2, op p.1 p.2 d) := by
  induction w generalizing u v with
  | nil => simp [eval_pair, eval_pair.go, op]
  | cons hd tl ih =>
    simp [eval_pair, eval_pair.go, op, ih]
    dsimp only [eval_pair] at ih
    rw [ih]
    rfl
theorem algebra_23819_final_version
    (n : ℕ) (hn : 0 < n)
    (ε : Ico 1 n → Fin 2)
    (a b : ℕ → ℤ)
    (ha₀ : a 0 = 1) (ha₁ : a 1 = 7)
    (ha_rec : ∀ i : Ico 1 n,
      a (i.val + 1) = if ε i = 0 then 2 * a (i.val - 1) + 3 * a i else 3 * a (i.val - 1) + a i)
    (hb₀ : b 0 = 1) (hb₁ : b 1 = 7)
    (hb_rec : ∀ (i : Ico 1 n) (ε_idx : Ico 1 n),
      ε_idx = Subtype.mk (n - i.val) (by
        simp_all only [Subtype.forall, mem_Ico, tsub_lt_self_iff, true_and]
        apply And.intro
        · rcases i with ⟨i_val, i_prop⟩
          simp only [mem_Ico] at i_prop
          rcases i_prop with ⟨h_le, h_lt⟩
          simp only [Subtype.coe_mk]
          rw [← Nat.lt_iff_add_one_le]
          omega
        · rcases i with ⟨i_val, i_prop⟩
          simp only [mem_Ico] at i_prop
          rcases i_prop with ⟨h_le, h_lt⟩
          simp only [Subtype.coe_mk]
          omega
      ) →
      b (i.val + 1) = if ε ε_idx = 0 then 2 * b (i.val - 1) + 3 * b i else 3 * b (i.val - 1) + b i)
    : a n = b n :=
by
  let ε_list := List.ofFn (fun i : Fin (n - 1) => ε ⟨i.val + 1, by
  simp
  have h1 : i < n - 1 := i.is_lt
  have h2 : (i : ℕ) + 1 < n := by 
    omega
  exact h2⟩)
  have a_n_eq_eval_word : a n = eval_word 1 7 ε_list := by
    have eval_word_eq_snd_eval_pair (u v) (w : List (Fin 2)) :
        eval_word u v w = (eval_pair u v w).2 := by
      induction w generalizing u v with
      | nil =>
        dsimp [eval_word, eval_pair]
      | cons d ds ih =>
        simp [eval_word, eval_pair, op, ih]
    have a_pair_eq_eval_pair : ∀ k ∈ Icc 0 (n - 1),
    (a k, a (k+1)) = eval_pair 1 7 (ε_list.take k) := by
      intro k hk
      induction k with
      | zero =>
        rw [List.take_zero]
        simp [eval_pair, ha₀, ha₁]
        rfl
      | succ k' ih =>
        have ih_clean := ih (by
          simp at hk
          simp only [mem_Icc]
          constructor
          · linarith
          · linarith [hk])
        have eval_pair_append_singleton (u v) (w : List (Fin 2)) (d : Fin 2) :
            eval_pair u v (w ++ [d]) = let p := eval_pair u v w; (p.2, op p.1 p.2 d) := by
          induction w generalizing u v with
          | nil => simp [eval_pair, eval_pair.go, op]
          | cons hd tl h_ind =>
            simp_rw [List.cons_append, eval_pair, eval_pair.go, op];
            dsimp only at h_ind
            simp [eval_pair, eval_pair.go, op] at h_ind
            rw [h_ind]
        have h_bounds : k' < ε_list.length := by
          unfold ε_list
          simp [List.length_ofFn]
          simp only [mem_Icc] at hk
          linarith [hk]
        have hh := eval_pair_append_singleton 1 7 (ε_list.take k') 
        rw [List.take_succ]
        rw [List.getElem?_eq_getElem h_bounds]
        simp only [Option.toList_some]
        rw [hh]
        dsimp
        rw [← ih_clean]
        simp [op]
        rw [ha_rec ⟨k' + 1, by {
          simp only [mem_Ico]
          constructor
          · exact Nat.succ_le_succ (Nat.zero_le k')
          · simp only [mem_Icc] at hk
            have h_upper := hk.2
            omega
        }⟩]
        simp
        congr
        simp [ε_list, List.get_ofFn, Fin.val_mk]
    rw [eval_word_eq_snd_eval_pair]
    have h_pair_eq_pre := a_pair_eq_eval_pair (n - 1) (by simp [hn])
    have h_take : ε_list.take (n - 1) = ε_list := by
      apply List.take_of_length_le
      rw [List.length_ofFn]
    have h_pair_eq : (a (n - 1), a n) = eval_pair 1 7 ε_list := by
      rw [h_take] at h_pair_eq_pre
      rw [show (n-1+1=n) by omega] at h_pair_eq_pre
      exact h_pair_eq_pre
    rw [← h_pair_eq]
  have b_n_eq_eval_word_reverse : b n = eval_word 1 7 ε_list.reverse := by
    let ε_list_rev := ε_list.reverse
    have b_pair_eq_eval_pair : ∀ k ∈ Icc 0 (n - 1),
      (b k, b (k + 1)) = eval_pair 1 7 (ε_list_rev.take k) := by
      intro k hk
      induction k with
      | zero =>
        rw [List.take_zero]
        simp [eval_pair, hb₀, hb₁]
        rfl
      | succ k' ih =>
        have ih_clean := ih (by simp at hk; simp only [mem_Icc]; constructor; linarith; linarith [hk])
        have h_bounds : k' < ε_list_rev.length := by
          unfold ε_list_rev ε_list
          simp [List.length_reverse, List.length_ofFn]
          simp only [mem_Icc] at hk
          linarith [hk]
        rw [List.take_succ]
        rw [List.getElem?_eq_getElem h_bounds]
        simp only [Option.toList_some]
        have eval_pair_append_singleton (u v) (w : List (Fin 2)) (d : Fin 2) :
            eval_pair u v (w ++ [d]) = let p := eval_pair u v w; (p.2, op p.1 p.2 d) := by
          induction w generalizing u v with
          | nil => simp [eval_pair, eval_pair.go, op]
          | cons hd tl h_ind =>
            simp_rw [List.cons_append, eval_pair, eval_pair.go, op];
            dsimp only at h_ind
            simp [eval_pair, eval_pair.go, op] at h_ind
            rw [h_ind]
        rw [eval_pair_append_singleton]
        rw [← ih_clean]
        simp [op]
        rw [hb_rec ⟨k' + 1, by {
          simp only [mem_Ico]
          constructor
          · exact Nat.succ_le_succ (Nat.zero_le k')
          · simp only [mem_Icc] at hk;have h_upper := hk.2; omega
        }⟩]
        case succ.ε_idx =>
          refine' ⟨n - (k' + 1), _⟩
          simp only [mem_Ico]
          constructor
          · 
            simp only [mem_Icc] at hk
            omega
          · 
            apply Nat.sub_lt_self
            · omega
            · simp only [mem_Icc] at hk;have h_lower:= hk.1;omega
        case succ.a =>
          rfl
        simp
        congr
        rw [eq_comm]
        dsimp [ε_list_rev]
        rw [List.getElem_reverse]
        rw [List.getElem_ofFn]
        congr
        simp [ε_list]
        simp [Finset.mem_Icc] at hk
        omega
    have eval_word_eq_snd_eval_pair (u v) (w : List (Fin 2)) :
        eval_word u v w = (eval_pair u v w).2 := by
      induction w generalizing u v with
      | nil =>
        dsimp [eval_word, eval_pair]
      | cons d ds ih =>
        simp [eval_word, eval_pair, op, ih]
    rw [eval_word_eq_snd_eval_pair]
    have h_pair_eq_pre := b_pair_eq_eval_pair (n - 1) (by simp [hn])
    have h_take : ε_list_rev.take (n - 1) = ε_list_rev := by
      apply List.take_of_length_le
      rw [List.length_reverse, List.length_ofFn]
    have h_pair_eq : (b (n - 1), b n) = eval_pair 1 7 ε_list_rev := by
      rw [h_take] at h_pair_eq_pre
      rw [show (n - 1 + 1 = n) by omega] at h_pair_eq_pre
      exact h_pair_eq_pre
    rw [← h_pair_eq]
  have eval_word_1_7_is_symmetric (w : List (Fin 2)) :
      eval_word 1 7 w = eval_word 1 7 w.reverse := by
    suffices P_and_Q : (eval_word 1 7 w = eval_word 1 7 w.reverse) ∧
                     ((eval_pair 1 7 w.reverse).1 = eval_word 2 1 w) from
      P_and_Q.1
    induction w with
    | nil => 
      constructor
      · simp [eval_word, eval_pair] 
      · simp [eval_word, eval_pair, eval_pair.go] 
    | cons d ds ih => 
      have h_P_ds := ih.1
      have h_Q_ds := ih.2
      constructor
      · 
        dsimp [eval_word, eval_pair, eval_pair.go] 
        rw [List.reverse_cons] 
        have h_rhs_expand : eval_word 1 7 (ds.reverse ++ [d]) =
            op (eval_pair 1 7 ds.reverse).1 (eval_pair 1 7 ds.reverse).2 d := by
          dsimp [eval_word]
          rw [eval_pair_append_singleton]
        rw [← eval_pair]
        rw [← eval_pair]
        rw [← eval_word]
        rw [← eval_word]
        rw [h_rhs_expand]
        rw [←eval_word, ← h_P_ds, h_Q_ds] 
        let X := eval_word 1 0 ds
        let Y := eval_word 0 1 ds
        have h_lhs : eval_word 7 (op 1 7 d) ds = 7 * X + (op 1 7 d) * Y := by
          rw [← eval_word_linearity 7 (op 1 7 d) 1 0 0 1]
          simp
        have h_rhs : op (eval_word 2 1 ds) (eval_word 1 7 ds) d =
                    op (2 * X + Y) (X + 7 * Y) d := by
          congr
          · unfold X Y;rw [← one_mul (eval_word 0 1 ds)];rw [← eval_word_linearity 2 1 1 0 0 1]; simp
          · unfold X Y;rw [← one_mul (eval_word 1 0 ds)];rw [← eval_word_linearity 1 7 1 0 0 1]; simp
        rw [h_lhs, h_rhs]
        fin_cases d <;> (simp [op]; ring)
      · 
        dsimp [eval_word]
        rw [List.reverse_cons, eval_pair_append_singleton]
        rw [← eval_word]
        rw [eval_word_2_1_cons]
        dsimp
        rw [← eval_word]
        rw [h_P_ds]
  rw [a_n_eq_eval_word, b_n_eq_eval_word_reverse]
  apply eval_word_1_7_is_symmetric