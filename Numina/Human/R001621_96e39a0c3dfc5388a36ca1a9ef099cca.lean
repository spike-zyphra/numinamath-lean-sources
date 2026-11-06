import Mathlib

open Finset

/-
  In this lemma, we prove that if a > b > 0, then A_n / A_{n+1} < B_n / B_{n+1},
  where A_n, B_n, A_{n+1}, and B_{n+1} are numbers in the number systems with respective bases a and b, as defined in the problem statement.
-/
lemma div_lt_div_of_base_lt_base {n : ℕ} (a b : ℕ) (ha : a > 0) (hb : b > 0) (hab : a > b)
    (hn : n > 0) (x : List ℕ) (hx : x.length = n + 1) 
    (A B A' B' : ℕ) (hA : Nat.digits a A = x.dropLast) (hB : Nat.digits b B = x.dropLast)
    (hA' : Nat.digits a A' = x) (hB' : Nat.digits b B' = x) :
    (A / A' : ℝ) < B / B' := by

  -- Note that x and x.dropLast are not empty lists, as they are digits in the number systems with bases a and b.
  have hx_ne_empty : x ≠ [] := by
    intro h
    simp [h] at hx

  -- 2. Suppose that $a>b$.
  -- Consider the polynomial $P(X)=x\_{1} X^{n-1}+x\_{2} X^{n-2}+$ $\cdots+x\_{n-1} X+x\_{n}$.
  let P (X : ℕ) : ℕ := Nat.ofDigits X x.dropLast

  --We have $A\_{n}=P(a), B\_{n}=P(b), A\_{n+1}=x\_{0} a^{n}+$ $P(a)$, and $B\_{n+1}=x\_{0} b^{n}+P(b)$.
  have hPa : P a = A := by
    simp [P, ←hA]
    exact Nat.ofDigits_digits a A

  have hPb : P b = B := by
    simp [P, ←hB]
    exact Nat.ofDigits_digits b B

  have hPa' : P a + (x.getLast hx_ne_empty) * a ^ n = A' := by
    simp [P]
    have hPa' : Nat.ofDigits a x = A' := by
      simp [P, ←hA']
      exact Nat.ofDigits_digits a A'
    rw [←hPa']
    have : x = x.dropLast ++ [x.getLast hx_ne_empty] := by
      exact Eq.symm (List.dropLast_concat_getLast hx_ne_empty)
    nth_rw 3 [this]
    rw [Nat.ofDigits_append]
    simp [hx]
    ring

  have hPb' : P b + (x.getLast hx_ne_empty) * b ^ n = B' := by
    simp [P]
    have hPb' : Nat.ofDigits b x = B' := by
      simp [P, ←hB']
      exact Nat.ofDigits_digits b B'
    rw [←hPb']
    have : x = x.dropLast ++ [x.getLast hx_ne_empty] := by
      exact Eq.symm (List.dropLast_concat_getLast hx_ne_empty)
    nth_rw 3 [this]
    rw [Nat.ofDigits_append]
    simp [hx]
    ring

  have hx_last_ne_zero : x.getLast hx_ne_empty ≠ 0 := by
    simp [←hA']
    apply Nat.getLast_digit_ne_zero
    intro h
    simp [h] at hA'
    simp [hA'] at hx

  have hx_dropLast_ne_empty : x.dropLast ≠ [] := by
    intro h
    have : x.dropLast.length = 0 := by
      simp [h]
    simp [hx] at this
    simp [this] at hn

  have hx_dropLast_last_ne_zero : x.dropLast.getLast hx_dropLast_ne_empty ≠ 0 := by
    simp [←hA]
    apply Nat.getLast_digit_ne_zero
    intro h
    simp [h] at hA
    simp [hA] at hx_dropLast_ne_empty

  have hx_dropLast_eq : x[n - 1] = x.dropLast.getLast hx_dropLast_ne_empty := by
    simp [List.getLast_eq_getElem, hx]

  --Now $A\_{n} / A\_{n+1}b$, we have that $a^{i}>b^{i}$ and hence $x\_{i} a^{n} b^{n-i} \geq x\_{i} b^{n} a^{n-i}$ (also, for $i \geq 1$ the inequality is strict).
  rw [←hPa', ←hPb', ←hPa, ←hPb]
  simp
  apply div_lt_div_iff₀ ?_ ?_ |>.mpr
  · apply sub_pos.mp
    ring_nf
    simp
    suffices h : ↑(P a) * ↑b ^ n * ↑(x.getLast hx_ne_empty) < ↑(P b) * ↑a ^ n* ↑(x.getLast hx_ne_empty)
    · norm_cast
      apply lt_of_eq_of_lt ?_ (lt_of_lt_of_eq h ?_)
      all_goals ring
    · -- Summing up all these inequalities for $i=1, \ldots, n$ we get $a^{n} P(b)>b^{n} P(a)$, which completes the proof for $a>b$.
      apply mul_lt_mul_of_pos_right
      · unfold P
        rw [Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_eq_sum_mapIdx]
        rw [←Fin.sum_univ_get, ←Fin.sum_univ_get]
        have : (∑ i : Fin (List.mapIdx (fun i a_1 ↦ a_1 * a ^ i) x.dropLast).length, (List.mapIdx (fun i a_1 ↦ a_1 * a ^ i) x.dropLast)[i.val]) * b ^ n =
            (∑ i : Fin (List.mapIdx (fun i a ↦ a * b ^ i) x.dropLast).length, (List.mapIdx (fun i a_1 ↦ a_1 * a ^ i) x.dropLast)[i.val]) * b ^ n := by
          congr 1
          rw [←Fin.sum_congr' (a := (List.mapIdx (fun i a ↦ a * b ^ i) x.dropLast).length)]
          apply Finset.sum_congr rfl
          intro i _
          simp
          simp
        rw [this, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_lt_sum
        · intro i _
          have hi : i ≤ n - 1 := by
            apply Nat.le_of_lt_succ
            apply lt_of_lt_of_eq i.2
            simp [hx]
            rw [Nat.sub_add_cancel]
            exact hn
          simp
          rw [mul_assoc, mul_assoc]
          apply mul_le_mul_of_nonneg_left
          · apply Nat.cast_le (α := ℝ)|>.mp
            apply sub_nonneg.mp
            trans b ^ i.val * a ^ i.val * (a ^ (n - i) - b ^ (n - i))
            · apply mul_nonneg
              · positivity
              · simp
                apply pow_le_pow_left₀
                · simp
                · simp
                  apply le_of_lt hab
            · apply le_of_eq
              rw [mul_sub]
              nth_rw 3 4 [show n = n - i + i by rw [Nat.sub_add_cancel]; apply le_trans hi; simp]
              rw [pow_add, pow_add]
              simp
              ring
          · simp
        · use ⟨n - 1, by simp [hx]; exact hn⟩
          simp
          rw [mul_assoc, mul_assoc]
          apply mul_lt_mul_of_pos_left
          · apply Nat.cast_lt (α := ℝ)|>.mp
            apply sub_pos.mp
            apply lt_of_lt_of_eq (b := b ^ (n - 1) * a ^ (n - 1) * (a - b : ℝ))
            · apply mul_pos
              · positivity
              · simp
                exact hab
            · simp
              nth_rw 4 6 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel]; exact hn]
              rw [pow_add, pow_add]
              ring
          · rw [hx_dropLast_eq]
            exact Nat.zero_lt_of_ne_zero hx_dropLast_last_ne_zero
      · exact Nat.zero_lt_of_ne_zero hx_last_ne_zero
  · positivity
  · positivity

/- 2. (ROM 1) ${ }^{\mathrm{IMO} 2}$ Let $a$ and $b$ be the bases of two number systems and let  $$ \begin{array}{ll} A_{n}={\overline{x_{1} x_{2} \ldots x_{n}}}^{(a)}, & A_{n+1}={\overline{x_{0} x_{1} x_{2} \ldots x_{n}}}^{(a)}, \\ B_{n}={\overline{x_{1} x_{2} \ldots x_{n}}}^{(b)}, & B_{n+1}={\overline{x_{0} x_{1} x_{2} \ldots x_{n}}}^{(b)}, \end{array} $$  be numbers in the number systems with respective bases $a$ and $b$, so that $x_{0}, x_{1}, x_{2}, \ldots, x_{n}$ denote digits in the number system with base $a$ as well as in the number system with base $b$. Suppose that neither $x_{0}$ nor $x_{1}$ is zero. Prove that $a>b$ if and only if  $$ \frac{A_{n}}{A_{n+1}}<\frac{B_{n}}{B_{n+1}} . $$ -/
theorem number_theory_24858 {n : ℕ} (a b : ℕ) (ha : a > 0) (hb : b > 0) (hn : n > 0)
    (x : List ℕ) (hx : x.length = n + 1)
    (A B A' B' : ℕ) (hA : Nat.digits a A = x.dropLast) (hB : Nat.digits b B = x.dropLast)
    (hA' : Nat.digits a A' = x) (hB' : Nat.digits b B' = x) :
    a > b ↔ (A / A' : ℝ) < B / B' := by

  constructor
  · -- apply the lemma we proved above
    intro h
    apply div_lt_div_of_base_lt_base a b ha hb h hn x hx A B A' B' hA hB hA' hB'
  · -- On the other hand, for $aB\_{n} / B\_{n+1}$, while for $a=b$ we have equality.
    -- Thus $A\_{n} / A\_{n+1}<$ $B\_{n} / B\_{n+1} \Leftrightarrow a>b$.
    intro h
    by_contra h'
    simp at h'
    rcases lt_or_eq_of_le h' with (h' | h')
    · obtain h' := div_lt_div_of_base_lt_base b a hb ha h' hn x hx B A B' A' hB hA hB' hA'
      apply lt_trans h at h'
      simp at h'
    · simp [h'] at hA hA'
      rw [←hA'] at hB'
      have : A' = B' := by exact Nat.digits_inj_iff.mp (id (Eq.symm hB'))
      rw [this] at h
      rw [←hA] at hB
      have : A = B := by exact Nat.digits_inj_iff.mp (id (Eq.symm hB))
      rw [this] at h
      simp at h
