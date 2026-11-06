import Mathlib

open Set Real

/- Let $S$ be the set of all points $t$ in the closed interval $[-1,1]$ such that for the sequence $x_{0}, x_{1}, x_{2}, \ldots$ defined by the equations $x_{0}=t, x_{n+1}=2 x_{n}^{2}-1$, there exists a positive integer $N$ such that $x_{n}=1$ for all $n \geq N$. Show that the set $S$ has infinitely many elements. -/
theorem algebra_607928 :
    Infinite {t : ℝ | t ∈ Icc (-1) 1 ∧ ∃ x : ℕ → ℝ, x 0 = t ∧ ∀ n, x (n + 1) = 2 * (x n)^2 - 1 ∧ ∃ N, ∀ n ≥ N, x n = 1} := by
        let S  : Set ℝ := {t : ℝ | t ∈ Icc (-1) 1 ∧ ∃ x : ℕ → ℝ, x 0 = t ∧ ∀ n, x (n + 1) = 2 * (x n)^2 - 1 ∧ ∃ N, ∀ n ≥ N, x n = 1}
        let f: ℕ → ℝ := fun m ↦ Real.cos (Real.pi / (2 ^ m))
        let Sp : Set ℝ := Set.range f

        -- Sp is infinite
        have Spinfi : Sp.Infinite := by
            apply Set.infinite_range_of_injective
            intro m1 m2 h

            simp [f] at h
            have h : (Real.pi / (2 ^ m1)) = (Real.pi / (2 ^ m2)) := by
                -- use the fact that f is injective
                apply Real.injOn_cos
                simp

                constructor
                positivity
                apply div_le_self; exact pi_nonneg;
                have powerge1 : 1≤ 2^m1 := by exact Nat.one_le_two_pow
                rify at powerge1; assumption
                constructor
                positivity
                apply div_le_self; exact pi_nonneg;
                have powerge2 : 1≤ 2^m2 := by exact Nat.one_le_two_pow
                rify at powerge2; assumption

                exact h


            field_simp at h;
            rcases h; tauto; exfalso; linarith [Real.pi_pos];


        -- Prove that Sp ⊆ S
        have SpsubS : Sp ⊆ S := by
            intro a ha; simp [Sp] at ha; simp [S]
            obtain ⟨m, hm⟩ := ha; simp [f] at hm

            constructor
            constructor
            rw [← hm]
            apply Real.neg_one_le_cos
            rw [← hm]
            exact cos_le_one (π / 2 ^ m)

            let x : ℕ → ℝ := Nat.rec (a) (fun n xn ↦ 2* xn ^2 -1)
            use x
            simp [x]

            -- x (m+1) = 1, so every n ≥ m+1 satisfies x n = 1 by cos (2*x) = 2*cos x ^2 - 1
            use (m+1)
            intro n hn

            have xsp12mulxs: ∀s :ℕ, x (s+1) = 2 * x s ^2 -1 := by simp [x]
            have : ∀ s : ℕ, x s = 1 →  x (s+1) = 1 := by
                intro s hs; rw [xsp12mulxs]; rw [hs]; norm_num
            have xst: ∀ s : ℕ, x s = 1 → ∀ c : ℕ,  x (s+c) = 1:= by
                intro s hs
                intro c
                induction' c with c hc
                ring_nf; exact hs
                rw [← add_assoc]; apply this; exact hc

            have xsp1: ∀ s : ℕ, x s = cos (2^s * π / 2^ m) := by
                intro s
                induction' s with s hs
                field_simp; simp [x]; symm; exact hm
                rw [xsp12mulxs]; rw [hs];
                rw [← Real.cos_two_mul];
                ring_nf

            have xmp1eq1: x (m+1) = 1 := by
                have : x (m+1) = cos (2 ^ (m+1) * π / 2 ^ m) := by apply xsp1 (m+1)
                rw [this]; rw [Real.cos_eq_one_iff];
                use 1; field_simp; ring
            have xneq1: x n = 1 := by
                have : x ((m+1)+(n - (m+1))) = 1 := by
                    apply xst (m+1) xmp1eq1;
                have : n =  ((m+1)+(n - (m+1))) := by omega
                rw [this]; assumption

            simp [x] at xneq1; assumption


        apply infinite_coe_iff.mpr; exact Infinite.mono SpsubS Spinfi
