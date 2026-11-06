import Mathlib

/- Prove that the set of positive integers cannot be partitioned into
three nonempty subsets such that for any two integers $x, y$ taken from
two different subsets, the number $x^{2}-x y+y^{2}$ belongs to the third subset. -/
theorem algebra_24912 (s t u : Set ℤ) (h₀ : s ∪ t ∪ u = {x : ℤ | 0 < x})
    (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (h₁ : s ∩ t = ∅) (h₂ : s ∩ u = ∅) (h₃ : t ∩ u = ∅)
    (f : ℤ → ℤ → ℤ) (hf : ∀ (x y : ℤ), f x y = x ^ 2 - x * y + y ^ 2)
    (h₄ : ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u)
    (h₅ : ∀ x ∈ s, ∀ y ∈ u, f x y ∈ t)
    (h₆ : ∀ x ∈ t, ∀ y ∈ u, f x y ∈ s) : False := by

    have fsymm (x y : ℤ) : f x y = f y x := by simp [hf]; ring

    /- w.l.o.g., change the order of A, B, C,
    so that $1 < b < c$, are their smallest elements
    Proof: take the smallest element by bruteforce-/
    have WLOG : ∃ (A B C : Set ℤ) (b c : ℤ),
        A ∪ B ∪ C = {x : ℤ | 0 < x} ∧ A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
        A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ ∧
        (∀ x ∈ A, ∀ y ∈ B, f x y ∈ C) ∧
        (∀ x ∈ A, ∀ y ∈ C, f x y ∈ B) ∧
        (∀ x ∈ B, ∀ y ∈ C, f x y ∈ A) ∧
        IsLeast A 1 ∧
        IsLeast B b ∧
        IsLeast C c ∧
        b > 1 ∧ c > b := by
        have in_stu : 1 ∈ s ∪ t ∪ u := by rw [h₀]; norm_num
        have ha : IsLeast (s ∪ t ∪ u) 1 := by
            rw [h₀]; constructor; norm_num; intro x; simp [Order.one_le_iff_pos]
        cases in_stu with
        | inl in_st => cases in_st with
            | inl in_s =>
                use s
                have minA : IsLeast s 1 := by
                    constructor; assumption
                    intro x hx
                    have : x ∈ s ∪ t ∪ u := by simp [hx]
                    exact ha.2 this
                obtain ⟨b, hb⟩ : ∃ b : ℤ, IsLeast (t ∪ u) b := by
                    apply BddBelow.exists_isLeast_of_nonempty
                    .   use 0; intro x hx
                        have : x ∈ s ∪ t ∪ u := by rw [Set.union_assoc]; simp [hx]
                        rw [h₀] at this; exact le_of_lt this
                    .   obtain ⟨x, hx⟩ : ∃ x : ℤ, x ∈ t := ht
                        use x; simp [hx]
                have bgt1 : b > 1 := by
                    have bge1 : b ≥ 1 := by apply ha.2; rw [Set.union_assoc, Set.mem_union]; right; exact hb.1
                    have bne1 : 1 ≠ b := by
                        by_contra beq1
                        have : 1 ∈ t ∪ u := by rw [beq1]; exact hb.1
                        cases this with
                        | inl in_t =>
                            have : 1 ∈ s ∩ t := by constructor <;> assumption
                            rw [h₁] at this; tauto
                        | inr in_u =>
                            have : 1 ∈ s ∩ u := by constructor <;> assumption
                            rw [h₂] at this; tauto
                    exact lt_of_le_of_ne bge1 bne1
                cases hb.1 with
                | inl in_t =>
                    use t, u, b
                    have minB : IsLeast t b := by
                        constructor; assumption
                        intro x hx
                        have : x ∈ t ∪ u := by simp [hx]
                        exact hb.2 this
                    obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast u c := by
                        apply BddBelow.exists_isLeast_of_nonempty
                        .   use 0; intro x hx
                            have : x ∈ s ∪ t ∪ u := by simp [hx]
                            rw [h₀] at this; exact le_of_lt this
                        .   exact hu
                    have cgtb : c > b := by
                        have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; right; exact hc.1
                        have cneb : b ≠ c := by
                            by_contra ceqb
                            have : b ∈ t ∩ u := by constructor; exact minB.1; rw [ceqb]; exact hc.1;
                            rw [h₃] at this; tauto
                        exact lt_of_le_of_ne cgeb cneb
                    use c
                | inr in_u =>
                    use u, t, b
                    have minB : IsLeast u b := by
                        constructor; assumption
                        intro x hx
                        have : x ∈ t ∪ u := by simp [hx]
                        exact hb.2 this
                    obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast t c := by
                        apply BddBelow.exists_isLeast_of_nonempty
                        .   use 0; intro x hx
                            have : x ∈ s ∪ t ∪ u := by simp [hx]
                            rw [h₀] at this; exact le_of_lt this
                        .   exact ht
                    have cgtb : c > b := by
                        have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; left; exact hc.1
                        have cneb : b ≠ c := by
                            by_contra ceqb
                            have : b ∈ t ∩ u := by constructor; rw [ceqb]; exact hc.1; exact minB.1;
                            rw [h₃] at this; tauto
                        exact lt_of_le_of_ne cgeb cneb
                    use c
                    constructor; rw [← h₀]; ext x; simp [Set.mem_union]; tauto
                    repeat (constructor; assumption)
                    constructor; rw [Set.inter_comm]; assumption
                    constructor; intro x hx y hy; exact h₅ x hx y hy
                    constructor; intro x hx y hy; exact h₄ x hx y hy
                    constructor; intro x hx y hy; rw [fsymm x y]; exact h₆ y hy x hx
                    repeat (constructor; assumption)
                    assumption
            | inr in_t =>
                use t
                have minA : IsLeast t 1 := by
                    constructor; assumption
                    intro x hx
                    have : x ∈ s ∪ t ∪ u := by simp [hx]
                    exact ha.2 this
                obtain ⟨b, hb⟩ : ∃ b : ℤ, IsLeast (s ∪ u) b := by
                    apply BddBelow.exists_isLeast_of_nonempty
                    .   use 0; intro x hx
                        have : x ∈ s ∪ t ∪ u := by rw [Set.union_comm s t, Set.union_assoc]; simp [hx]
                        rw [h₀] at this; exact le_of_lt this
                    .   obtain ⟨x, hx⟩ : ∃ x : ℤ, x ∈ s := hs
                        use x; simp [hx]
                have bgt1 : b > 1 := by
                    have bge1 : b ≥ 1 := by apply ha.2; rw [Set.union_assoc, Set.union_comm t u, ← Set.union_assoc, Set.mem_union]; left; exact hb.1
                    have bne1 : 1 ≠ b := by
                        by_contra beq1
                        have : 1 ∈ s ∪ u := by rw [beq1]; exact hb.1
                        cases this with
                        | inl in_s =>
                            have : 1 ∈ s ∩ t := by constructor <;> assumption
                            rw [h₁] at this; tauto
                        | inr in_u =>
                            have : 1 ∈ t ∩ u := by constructor <;> assumption
                            rw [h₃] at this; tauto
                    exact lt_of_le_of_ne bge1 bne1
                cases hb.1 with
                | inl in_s =>
                    use s, u, b
                    have minB : IsLeast s b := by
                        constructor; assumption
                        intro x hx
                        have : x ∈ s ∪ u := by simp [hx]
                        exact hb.2 this
                    obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast u c := by
                        apply BddBelow.exists_isLeast_of_nonempty
                        .   use 0; intro x hx
                            have : x ∈ s ∪ t ∪ u := by simp [hx]
                            rw [h₀] at this; exact le_of_lt this
                        .   exact hu
                    have cgtb : c > b := by
                        have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; right; exact hc.1
                        have cneb : b ≠ c := by
                            by_contra ceqb
                            have : b ∈ s ∩ u := by constructor; exact minB.1; rw [ceqb]; exact hc.1;
                            rw [h₂] at this; tauto
                        exact lt_of_le_of_ne cgeb cneb
                    use c
                    constructor; rw [← h₀]; ext x; simp [Set.mem_union]; tauto
                    repeat (constructor; assumption)
                    constructor; rw [Set.inter_comm]; assumption
                    repeat (constructor; assumption)
                    constructor; intro x hx y hy; rw [fsymm x y]; exact h₄ y hy x hx
                    constructor; intro x hx y hy; exact h₆ x hx y hy
                    constructor; intro x hx y hy; exact h₅ x hx y hy
                    repeat (constructor; assumption)
                    assumption
                | inr in_u =>
                    use u, s, b
                    have minB : IsLeast u b := by
                        constructor; assumption
                        intro x hx
                        have : x ∈ s ∪ u := by simp [hx]
                        exact hb.2 this
                    obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast s c := by
                        apply BddBelow.exists_isLeast_of_nonempty
                        .   use 0; intro x hx
                            have : x ∈ s ∪ t ∪ u := by simp [hx]
                            rw [h₀] at this; exact le_of_lt this
                        .   exact hs
                    have cgtb : c > b := by
                        have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; left; exact hc.1
                        have cneb : b ≠ c := by
                            by_contra ceqb
                            have : b ∈ s ∩ u := by constructor; rw [ceqb]; exact hc.1; exact minB.1
                            rw [h₂] at this; tauto
                        exact lt_of_le_of_ne cgeb cneb
                    use c
                    constructor; rw [← h₀]; ext x; simp [Set.mem_union]; tauto
                    repeat (constructor; assumption)
                    repeat (constructor; rw [Set.inter_comm]; assumption)
                    constructor; intro x hx y hy; exact h₆ x hx y hy
                    constructor; intro x hx y hy; rw [fsymm x y]; exact h₄ y hy x hx
                    constructor; intro x hx y hy; rw [fsymm x y]; exact h₅ y hy x hx
                    repeat (constructor; assumption)
                    assumption
        | inr in_u =>
            use u
            have minA : IsLeast u 1 := by
                constructor; assumption
                intro x hx
                have : x ∈ s ∪ t ∪ u := by simp [hx]
                exact ha.2 this
            obtain ⟨b, hb⟩ : ∃ b : ℤ, IsLeast (s ∪ t) b := by
                apply BddBelow.exists_isLeast_of_nonempty
                .   use 0; intro x hx
                    have : x ∈ s ∪ t ∪ u := by simp [hx]
                    rw [h₀] at this; exact le_of_lt this
                .   obtain ⟨x, hx⟩ : ∃ x : ℤ, x ∈ s := hs
                    use x; simp [hx]
            have bgt1 : b > 1 := by
                have bge1 : b ≥ 1 := by apply ha.2; rw [Set.mem_union]; left; exact hb.1
                have bne1 : 1 ≠ b := by
                    by_contra beq1
                    have : 1 ∈ s ∪ t := by rw [beq1]; exact hb.1
                    cases this with
                    | inl in_s =>
                        have : 1 ∈ s ∩ u := by constructor <;> assumption
                        rw [h₂] at this; tauto
                    | inr in_t =>
                        have : 1 ∈ t ∩ u := by constructor <;> assumption
                        rw [h₃] at this; tauto
                exact lt_of_le_of_ne bge1 bne1
            cases hb.1 with
            | inl in_s =>
                use s, t, b
                have minB : IsLeast s b := by
                    constructor; assumption
                    intro x hx
                    have : x ∈ s ∪ t := by simp [hx]
                    exact hb.2 this
                obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast t c := by
                    apply BddBelow.exists_isLeast_of_nonempty
                    .   use 0; intro x hx
                        have : x ∈ s ∪ t ∪ u := by simp [hx]
                        rw [h₀] at this; exact le_of_lt this
                    .   exact ht
                have cgtb : c > b := by
                    have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; right; exact hc.1
                    have cneb : b ≠ c := by
                        by_contra ceqb
                        have : b ∈ s ∩ t := by constructor; exact minB.1; rw [ceqb]; exact hc.1
                        rw [h₁] at this; tauto
                    exact lt_of_le_of_ne cgeb cneb
                use c
                constructor; rw [← h₀]; ext x; simp [Set.mem_union]; tauto
                repeat (constructor; assumption)
                repeat (constructor; rw [Set.inter_comm]; assumption)
                constructor; assumption
                constructor; intro x hx y hy; rw [fsymm x y]; exact h₅ y hy x hx
                constructor; intro x hx y hy; rw [fsymm x y]; exact h₆ y hy x hx
                constructor; intro x hx y hy; exact h₄ x hx y hy
                repeat (constructor; assumption)
                assumption
            | inr in_t =>
                use t, s, b
                have minB : IsLeast t b := by
                    constructor; assumption
                    intro x hx
                    have : x ∈ s ∪ t := by simp [hx]
                    exact hb.2 this
                obtain ⟨c, hc⟩ : ∃ c : ℤ, IsLeast s c := by
                    apply BddBelow.exists_isLeast_of_nonempty
                    .   use 0; intro x hx
                        have : x ∈ s ∪ t ∪ u := by simp [hx]
                        rw [h₀] at this; exact le_of_lt this
                    .   exact hs
                have cgtb : c > b := by
                    have cgeb : c ≥ b := by apply hb.2; rw [Set.mem_union]; left; exact hc.1
                    have cneb : b ≠ c := by
                        by_contra ceqb
                        have : b ∈ s ∩ t := by constructor; rw [ceqb]; exact hc.1; exact in_t
                        rw [h₁] at this; tauto
                    exact lt_of_le_of_ne cgeb cneb
                use c
                constructor; rw [← h₀]; ext x; simp [Set.mem_union]; tauto
                repeat (constructor; assumption)
                repeat (constructor; rw [Set.inter_comm]; assumption)
                constructor; intro x hx y hy; rw [fsymm x y]; exact h₆ y hy x hx
                constructor; intro x hx y hy; rw [fsymm x y]; exact h₅ y hy x hx
                constructor; intro x hx y hy; rw [fsymm x y]; exact h₄ y hy x hx
                repeat (constructor; assumption)
                assumption
    rcases WLOG with ⟨A, B, C, b, c, hABC, hA, hB, hC, hAB, hAC, hBC,
        h1, h2, h3, minA, minB, minC, hb1, hcb⟩





    /- exclusion lemma:
    $x, y$, and $x+y$ cannot belong to three different sets
    Proof: The number $f(x, x+y)=f(y, x+y)$ must belong to both the
    set containing $y$ and the set containing $x$, a contradiction. -/
    have ex_AB : ∀ x ∈ A, ∀ y ∈ B, x + y ∉ C := by
        intro x hx y hy
        by_contra h
        specialize h2 x hx (x + y) h
        specialize h3 y hy (x + y) h
        have ept: x ^ 2 + x * y + y ^ 2 ∈ A ∩ B := by
            rw [show f x (x + y) = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h2
            rw [show f y (x + y) = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h3
            constructor <;> tauto
        rw [hAB] at ept; tauto
    have ex_BC : ∀ x ∈ B, ∀ y ∈ C, x + y ∉ A := by
        intro x hx y hy
        by_contra h
        specialize h1 (x + y) h x hx
        specialize h2 (x + y) h y hy
        have ept: x ^ 2 + x * y + y ^ 2 ∈ B ∩ C := by
            rw [show f (x + y) x = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h1
            rw [show f (x + y) y = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h2
            constructor <;> tauto
        rw [hBC] at ept; tauto
    have ex_AC : ∀ x ∈ A, ∀ y ∈ C, x + y ∉ B := by
        intro x hx y hy
        by_contra h
        specialize h1 x hx (x + y) h
        specialize h3 (x + y) h y hy
        have ept: x ^ 2 + x * y + y ^ 2 ∈ A ∩ C := by
            rw [show f x (x + y) = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h1
            rw [show f (x + y) y = x ^ 2 + x * y + y ^ 2 by simp [hf]; ring] at h3
            constructor <;> tauto
        rw [hAC] at ept; tauto

    /- The subset C must contain a multiple l * b of b, and l > 1-/
    have lemma2 : ∃ k : ℤ, k > 1 ∧ k * b ∈ C := by
        let r := (c % b)
        have : r = 0 ∨ (0 < r ∧ r < b) := by
            obtain ⟨rge0, rltb⟩ : 0 ≤ r ∧ r < b := by
                constructor
                .   unfold r; exact Int.emod_nonneg _ (by linarith)
                .   unfold r; apply Int.emod_lt_of_pos _ (by linarith)
            cases eq_or_lt_of_le rge0 with
            | inl req0 => left; tauto
            | inr rgt0 => right; exact ⟨rgt0, rltb⟩
        cases this with
        | inl req0 =>

            /- if r = 0, use k := (c / b)
                Proof: c > b so k > 1, and k * b = c ∈ C -/
            let k := (c / b); use k
            have eqc: k * b = c := by
                rw [← Int.ediv_add_emod c b]
                have : c % b = 0 := req0
                unfold k; rw [this]; ring
            constructor
            .   unfold k
                apply Int.lt_ediv_of_mul_lt
                linarith; use k; rw [← eqc]; ring
                simp; exact hcb
            .   rw [eqc]; exact minC.1
        | inr rne0 =>

            /- if not, use k := (f (c - r) b) / b
                Proof: c - r = lb ∈ A, l ≥ 1
                f (c - r) b = (lb)^2 - lb^2 + b^2 = (l^2 - l + 1) * b^2 ∈ C
                now k = (l^2 - l + 1)*b > 1, and kb ∈ C -/
            obtain ⟨l, ⟨hl1, hl2⟩⟩ : ∃ l : ℤ, c - r = l * b ∧ l ≥ 1 := by
                use (c / b)
                constructor
                .   nth_rewrite 1 [← Int.ediv_add_emod c b]; unfold r; ring
                .   apply Int.le_ediv_of_mul_le
                    linarith; simp; linarith
            let k := (l * (l - 1) + 1) * b; use k
            have kbin_C : f (c - r) b ∈ C := by
                have in_A : c - r ∈ A := by
                    have nin_B : c - r ∉ B := by
                        have : r ∈ A := by
                            have nin_B : r ∉ B := by
                                by_contra in_B
                                have : b ≤ r := minB.2 in_B
                                exact not_le_of_gt rne0.2 this
                            have nin_C : r ∉ C := by
                                by_contra in_C
                                have : c ≤ r := minC.2 in_C
                                exact not_le_of_gt (lt_trans rne0.2 hcb) this
                            have in_ABC : r ∈ A ∪ B ∪ C := by rw [hABC]; exact rne0.1
                            cases in_ABC with
                            | inl in_AB => cases in_AB <;> tauto
                            | inr in_C => tauto
                        by_contra in_B
                        specialize ex_AB r this (c - r) in_B
                        simp at ex_AB; exact ex_AB minC.1
                    have nin_C : c - r ∉ C := by
                        by_contra in_C
                        have : c ≤ c - r := minC.2 in_C
                        exact not_le_of_gt (by linarith) this
                    have in_ABC : c - r ∈ A ∪ B ∪ C := by
                        have : c - r > 0 := by
                            calc
                                c - r > b - r := by simp [hcb]
                                _ > 0 := by simp [rne0.2]
                        rw [hABC]; tauto
                    cases in_ABC with
                    | inl in_AB => cases in_AB <;> tauto
                    | inr in_C => tauto
                exact h1 (c - r) in_A b minB.1

            have eval_kb : f (c - r) b = (l * (l - 1) + 1) * b * b := by
                simp [hf]; rw [hl1]; ring
            constructor
            .   suffices l * (l - 1) + 1 ≥ 1 by
                    unfold k
                    calc
                        (l * (l - 1) + 1) * b ≥ 1 * b := by apply mul_le_mul_of_nonneg_right this; linarith
                        _ > 1 := by simp [hb1]
                simp; exact mul_nonneg
                    (le_trans (by norm_num) hl2) (by simp [hl2])
            unfold k; rw [← eval_kb]; tauto

    /- let k * b be the smallest such multiple -/
    let S : Set ℤ := {k : ℤ | k > 1 ∧ k * b ∈ C}
    have minK : ∃ k : ℤ, IsLeast S k := by
        apply BddBelow.exists_isLeast_of_nonempty
        .   use 1; intro a ha
            exact le_of_lt ha.1
        .   exact lemma2
    rcases minK with ⟨k, hk⟩

    /- auxiliary lemma: (k - 1) * b is in B,
    Proof: using exclusion lemma-/
    have k1b_in_B : (k - 1) * b ∈ B := by

        /- = k * b - b, so not in A (exclusion lemma) -/
        have nin_A : (k - 1) * b ∉ A := by
            by_contra h
            specialize ex_AB ((k - 1) * b) h b minB.1
            rw [show (k - 1) * b + b = k * b by ring] at ex_AB
            exact ex_AB hk.1.2

        /- if (k - 1) > 1, k is taken to be minimum, so impossible;
            if k is 2, b is also not in C-/
        have nin_C : (k - 1) * b ∉ C := by
            by_contra h
            have in_S : (k - 1) ∈ S := by
                unfold S; simp
                constructor
                .   by_contra kle2
                    have : k = 2 := by
                        apply le_antisymm
                        .   push_neg at kle2; linarith
                        .   calc
                                2 = 1 + 1 := by rfl
                                _ ≤ k := hk.1.1
                    simp [this] at h
                    exact not_le_of_gt hcb (minC.2 h)
                .   exact h
            exact not_le_of_gt (by simp) (hk.2 in_S)

        /- must in B -/
        have in_ABC : (k - 1) * b ∈ A ∪ B ∪ C := by
            have : (k - 1) * b > 0 := by
                simp [hk.1.1]; exact lt_trans (by norm_num) hb1
            rw [hABC]; tauto
        cases in_ABC with
            | inl in_AB => cases in_AB <;> tauto
            | inr in_C => tauto

    /- auxiliary lemma: b - 1 is in B
        Proof: the minimum of B and C are all greater than b - 1, so b - 1 is in A -/
    have b1_in_A : b - 1 ∈ A := by
        by_contra h
        have : b - 1 ∈ A ∪ B ∪ C := by rw [hABC]; simp [hb1]
        cases this with
            | inl in_AB => cases in_AB with
                | inl in_A => tauto
                | inr in_B => {
                    have lst : b ≤ b - 1:= minB.2 in_B
                    exact not_le_of_gt (by norm_num) lst
                }
            | inr in_C => {
                have : b - 1 < c := by exact lt_trans (by simp) hcb
                have lst : c ≤ b - 1 := minC.2 in_C
                exact not_le_of_gt this lst
            }

    /- show by induction (n * k - 1) * b + 1, n * k * b + 1 ∈ A for all n > 0.
        (note: the second assertion depends on the first) -/
    have lemma3 (n : ℤ) (pn : 0 < n) :
        (n * k - 1) * b + 1 ∈ A ∧ n * k * b + 1 ∈ A := by
        -- lift n to ℕ+ using pn
        lift n to ℕ using pn.le
        induction' n with n ih
        .   exfalso; tauto

        /- induction base1: (k - 1) * b + 1 ∈ A -/
        have step1 : (k - 1) * b + 1 ∈ A := by

            /- = k * b - (b - 1), so not in B (exclusion lemma) -/
            have nin_B : (k - 1) * b + 1 ∉ B := by
                have : (k - 1) * b + 1 = k * b - (b - 1) := by ring
                by_contra h; rw [this] at h
                specialize ex_AB (b - 1) b1_in_A (k * b - (b - 1)) h
                simp at ex_AB; exact ex_AB hk.1.2

            /- not in C (exclusion lemma) -/
            have nin_C : (k - 1) * b + 1 ∉ C := by
                have : (k - 1) * b + 1 = 1 + (k - 1) * b := by ring
                rw [this]
                specialize ex_AB 1 minA.1 ((k - 1) * b) k1b_in_B; tauto

            /- so must be in A -/
            have in_ABC : (k - 1) * b + 1 ∈ A ∪ B ∪ C := by
                have : (k - 1) * b + 1 > 0 := by
                    have : (k - 1) > 0 := by simp [hk.1.1]
                    positivity
                rw [hABC]; tauto
            cases in_ABC with
            | inl in_AB => cases in_AB <;> tauto
            | inr in_C => tauto

        cases n with
        | zero =>
            constructor
            .   simp [step1]

            /- induction base2: k * b + 1 ∈ A -/
            .   simp

                /- not in B, (exclusion lemma) -/
                have nin_B : k * b + 1 ∉ B := by
                    rw [show k * b + 1 = 1 + k * b by ring]
                    specialize ex_AC 1 minA.1 (k * b) hk.1.2; tauto

                /- = ((k - 1) * b + 1) + b, so not in C (exclusion lemma) -/
                have nin_C : k * b + 1 ∉ C := by
                    rw [show k * b + 1 = (k - 1) * b + 1 + b by ring]
                    specialize ex_AB ((k - 1) * b + 1) step1 b minB.1; tauto

                /- so must be in A -/
                have in_ABC : k * b + 1 ∈ A ∪ B ∪ C := by
                    have : k * b + 1 > 0 := by
                        have : k * b > 0 := Int.mul_pos
                            (lt_trans (by norm_num) hk.1.1) (lt_trans (by norm_num) hb1)
                        positivity
                    rw [hABC]; tauto
                cases in_ABC with
                | inl in_AB => cases in_AB <;> tauto
                | inr in_C => tauto

        | succ n' =>
        rcases ih (by simp [pn]) with ⟨ih1, ih2⟩
        let n := n' + 1; have simple : n' + 1 = n:= rfl
        rw [simple] at ih1 ih2 ⊢

        /- ((n + 1) * k - 1) * b + 1 ∈ A -/
        have step1 : ((n + 1) * k - 1) * b + 1 ∈ A := by
            let TODO := ((n + 1) * k - 1) * b + 1

            /- = (n * k * b + 1) + (k - 1) * b, so not in C (exclusion lemma) -/
            have nin_C : TODO ∉ C := by
                rw [show TODO = (n * k * b + 1) + (k - 1) * b by ring]
                specialize ex_AB (n * k * b + 1) ih2 ((k - 1) * b : ℤ) k1b_in_B; tauto

            /- = ((n * k - 1) * b + 1) + k * b, so not in B (exclusion lemma) -/
            have nin_B : TODO ∉ B := by
                rw [show TODO = ((n * k - 1) * b + 1) + k * b by ring]
                specialize ex_AC ((n * k - 1) * b + 1) ih1 (k * b : ℤ) hk.1.2; tauto

            /- so must be in A -/
            have in_ABC : TODO ∈ A ∪ B ∪ C:= by
                have : TODO > 0 := by
                    have : (n + 1) * k - 1 > 0 := by
                        simp; have hn : (1 : ℤ) < (n + 1) := by simp
                        calc
                            1 < 1 * k := by rw [one_mul]; exact hk.1.1
                            _ < (n + 1) * k  := by rw [mul_lt_mul_right]; exact hn; exact lt_trans (by norm_num) hk.1.1
                    positivity
                rw [hABC]; tauto
            cases in_ABC with
            | inl in_AB => cases in_AB <;> tauto
            | inr in_C => tauto
        constructor
        .   exact step1

        /- (n + 1) * k * b + 1 ∈ A -/
        .   let TODO := (n + 1) * k * b + 1

            /-  = (((n + 1) * k - 1) * b + 1) + b , so not in C (exclusion lemma) -/
            have nin_C : TODO ∉ C := by
                rw [show TODO = ((n + 1) * k - 1) * b + 1 + b by ring]
                specialize ex_AB (((n + 1) * k - 1) * b + 1) step1 b minB.1; tauto

            /-  = (n * k * b + 1) + k * b , so not in B (exclusion lemma) -/
            have nin_B : TODO ∉ B := by
                rw [show TODO = (n * k * b + 1) + k * b by ring]
                specialize ex_AC (n * k * b + 1) ih2 (k * b) hk.1.2; tauto

            /- so must be in A -/
            have in_ABC : TODO ∈ A ∪ B ∪ C:= by
                have : (n + 1) * k * b > 0 := by
                    apply mul_pos; apply mul_pos; norm_num
                    exact lt_trans (by norm_num) hk.1.1
                    exact lt_trans (by norm_num) hb1
                have : TODO > 0 := by positivity
                rw [hABC]; tauto
            cases in_ABC with
            | inl in_AB => cases in_AB <;> tauto
            | inr in_C => tauto

    /- construct T = f (k * b) (k * b + 1) ∈ A ∩ B = ∅, thus a contradiction -/
    let T := f (k * b + 1) (k * b)
    have in_AB : T ∈ A ∩ B := by
        constructor

        -- T = (k * b + 1) * k * b + 1 in A by lemma3
        .   have in_A : T = (k * b + 1) * k * b + 1:= by unfold T; simp [hf]; ring
            have : k * b + 1 > 0 := by
                have : k * b > 0 := mul_pos
                    (lt_trans (by norm_num) hk.1.1) (lt_trans (by norm_num) hb1)
                positivity
            specialize lemma3 (k * b + 1) this
            rw [in_A]; tauto

        -- k * b ∈ C, k * b + 1 ∈ A, so T ∈ B by assumption
        .   have in_A : k * b + 1 ∈ A := by
                specialize lemma3 1 (by norm_num); simp at lemma3; exact lemma3.2
            unfold T; exact h2 (k * b + 1) in_A (k * b) hk.1.2

    rw [hAB] at in_AB; tauto
