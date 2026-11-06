import Mathlib

open Real
/-
Prouver que, pour tout entier $n \geq 2$, on a : $\sum_{k=2}^{n} \frac{1}{\sqrt[k]{(2 k)!}} \geq \frac{n-1}{2 n+2}$.
N.B. Si $a>0$, on note $\sqrt[k]{a}$ l'unique nombre réel $b>0$ tel que $b^{k}=a$.
-/
theorem inequalities_605034 {n : ℕ} (hn : n ≥ 2) :
    ∑ k ∈ Finset.Icc 2 n, 1 / ((2 * k).factorial : ℝ) ^ (1 / k : ℝ) ≥ (n - 1) / (2 * n + 2) := by
  -- We reason by induction on $n \geq 2$.
  induction n, hn using Nat.le_induction
  · -- For $n=2$, we have $\frac{1}{\sqrt{24}} &gt; \frac{1}{6}$.
    simp
    have : Nat.factorial 4 = 24 := rfl
    norm_num
    rw [this, inv_eq_one_div]
    apply div_le_div_iff₀ ?_ ?_|>.mpr
    · norm_num
      rw [←sqrt_eq_rpow]
      apply sqrt_le_iff.mpr
      constructor
      · simp
      · norm_num
    · simp
    · apply rpow_pos_of_pos
      norm_cast
  · rename_i n hn ih
    -- Suppose the desired inequality holds for the value $n-1 \geq 2$.
    -- For the value $n$, the right-hand side increases by $\frac{n-1}{2 n+2} - \frac{n-2}{2 n} = \frac{1}{n(n+1)}$.
    -- According to the induction hypothesis, it suffices to prove that $\frac{1}{\sqrt[n]{(2 n)!}} \geq \frac{1}{n(n+1)}$.
    suffices h : 1 / ((n + 1) * (n + 2) : ℝ) ≤ 1 / ((2 * (n + 1)).factorial : ℝ) ^ (1 / (n + 1) : ℝ)
    · rw [←Nat.Icc_insert_succ_right]
      simp
      trans (↑n - 1) / (2 * ↑n + 2 : ℝ) + 1 / ((n + 1) * (n + 2) : ℝ)
      · apply le_of_eq
        field_simp
        ring
      rw [add_comm]
      apply add_le_add
      · simp at h
        simp
        exact h
      · simp at ih
        exact ih
      · exact Nat.le_add_right_of_le hn
    · rw [←inv_eq_one_div, ←inv_eq_one_div]
      apply inv_le_inv₀ ?_ ?_ |>.mpr
      · apply rpow_le_rpow_iff (z := (n + 1 : ℝ)) ?_ ?_ ?_ |>.mp
        · -- For $k=1,2, \cdots, n$, we have $(n-k)(n-k+1) \geq 0$, so $0 \leq k(2 n-k+1) \leq n(n+1)$.
          -- By multiplying these inequalities term by term, we get $(2 n)! \leq (n(n+1))^{n}$, from which the conclusion follows.
          rw [←rpow_mul, div_mul_cancel₀, rpow_one]
          · norm_cast
            clear ih hn
            have h₁ : (2 * (n + 1)).factorial = ∏ i ∈ Finset.Icc 1 (n + 1), i * (2 * n + 3 - i) := by
              rw [Finset.prod_mul_distrib]
              have : ∏ x ∈ Finset.Icc 1 (n + 1), (2 * n + 3 - x) = ∏ x ∈ Finset.Icc (n + 2) (2 * n + 2), x := by
                have : Finset.Icc (n + 2) (2 * n + 2) = (Finset.Icc 1 (n + 1)).image (fun x => 2 * n + 3 - x) := by
                  ext x
                  simp
                  constructor <;> intro h
                  · use 2 * n + 3 - x
                    constructor
                    · constructor
                      · trans 2 * n + 3 - (2 * n + 2)
                        · simp
                        · rel [h.2]
                      · trans 2 * n + 3 - (n + 2)
                        · rel [h.1]
                        · simp
                          apply le_of_eq
                          ring
                    · rw [Nat.sub_sub_self]
                      apply le_trans h.2
                      simp
                  · obtain ⟨a, ha1, ha2⟩ := h
                    rw [←ha2]
                    constructor
                    · trans 2 * n + 3 - (n + 1)
                      · simp
                        apply Nat.le_sub_of_add_le
                        apply le_of_eq
                        ring
                      · rel [ha1.2]
                    · trans 2 * n + 3 - 1
                      · rel [ha1.1]
                      · simp
                rw [this, Finset.prod_image]
                intro _ hx _ hy hf
                apply tsub_right_inj ?_ ?_ |>.mp hf
                · simp at hx
                  apply le_trans hx.2
                  rw [show 2 * n + 3 = n + 1 + (n + 2) by ring]
                  exact Nat.le_add_right (n + 1) (n + 2)
                · simp at hy
                  apply le_trans hy.2
                  rw [show 2 * n + 3 = n + 1 + (n + 2) by ring]
                  exact Nat.le_add_right (n + 1) (n + 2)
              rw [this]
              rw [←Finset.prod_union]
              · have : Finset.Icc 1 (n + 1) ∪ Finset.Icc (n + 2) (2 * n + 2) = Finset.Ico 1 (2 * (n + 1) + 1) := by
                  ext x
                  simp
                  constructor <;> intro h
                  · rcases h with h | h
                    · simp [h.1]
                      apply lt_of_le_of_lt h.2
                      rw [show 2 * (n + 1) + 1 = n + 1 +(n + 2) by ring]
                      refine Nat.lt_add_of_pos_right ?h.mp.inl.h
                      simp
                    · constructor
                      · apply le_trans ?_ h.1
                        simp
                      · rw [mul_add, mul_one]
                        apply Nat.lt_add_one_of_le
                        exact h.2
                  · by_cases h' : x ≤ n + 1
                    · simp [h.1, h']
                    · push_neg at h'
                      right
                      constructor
                      · apply Nat.add_one_le_of_lt h'
                      · apply Nat.le_of_lt_add_one
                        exact h.2
                rw [this, ←Finset.prod_Ico_id_eq_factorial]
              · refine Finset.disjoint_left.mpr ?_
                intro a ha
                simp at ha ⊢
                intro h
                obtain ha := ha.2
                apply le_trans h at ha
                simp at ha
            rw [h₁]
            trans ∏ i ∈ Finset.Icc 1 (n + 1), (n + 1) * (n + 2)
            · apply Finset.prod_le_prod
              · intro _ hi
                simp at hi
                apply mul_nonneg
                · simp
                · trans 2 * n + 3 - (n + 1)
                  · simp
                  · rel [hi.2]
              · intro i hi
                simp at hi
                apply Nat.cast_le (α := ℤ) |>.mp
                simp
                apply sub_nonneg.mp
                rw [Nat.cast_sub, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
                trans (n - i + 1) * (n - i + 2 : ℤ)
                · apply mul_nonneg
                  · trans n - (n + 1 : ℤ) + 1
                    · simp
                    · obtain h := Nat.cast_le (α := ℤ) |>.mpr hi.2
                      simp at h
                      rel [h]
                  · trans n - (n + 1 : ℤ) + 2
                    · simp
                    · obtain h := Nat.cast_le (α := ℤ) |>.mpr hi.2
                      simp at h
                      rel [h]
                · apply le_of_eq
                  ring
                · trans n + 1
                  · exact hi.2
                  · simp
                    rw [show 2 = 1 + 1 by rfl, add_mul, one_mul, add_assoc]
                    exact Nat.le_add_right n (n + (1 + 1))
            · rw [Finset.prod_const]
              apply le_of_eq
              congr
              simp
          · norm_cast
          · norm_cast
            exact Nat.zero_le (2 * (n + 1)).factorial
        · apply rpow_nonneg
          norm_cast
          exact Nat.zero_le (2 * (n + 1)).factorial
        · norm_cast
          simp
        · norm_cast
          exact Nat.zero_lt_succ n
      · norm_cast
        apply mul_pos
        all_goals simp
      · apply rpow_pos_of_pos
        norm_cast
        apply Nat.factorial_pos
