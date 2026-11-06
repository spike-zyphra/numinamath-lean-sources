import Mathlib

open Real Set
open scoped BigOperators

/- Let $a_{0}, a_{1}, \ldots, a_{n}$ be numbers from the interval $(0, \pi / 2)$ such that $\tan \left(a_{0}-\frac{\pi}{4}\right)+$ $\tan \left(a_{1}-\frac{\pi}{4}\right)+\cdots+\tan \left(a_{n}-\frac{\pi}{4}\right) \geq n-1$. Prove that  $$ \tan a_{0} \tan a_{1} \cdots \tan a_{n} \geq n^{n+1} $$ -/
theorem inequalities_606132 {n : ℕ} (a : Fin (n + 1) → ℝ) (ha : ∀ i, a i ∈ Ioo 0 (π / 2)) (h : ∑ i, tan (a i - π/4) ≥ n - 1) :
    ∏ i, tan (a i) ≥ n ^ (n+1) := by
  -- Let $x_{i}=\tan \left(a_{i}-\frac{\pi}{4}\right)$.
  let x (i : Fin (n + 1)) := tan (a i - π / 4)
  -- Prove that $a_i - \frac{\pi}{4}$ is in the interval $(-\frac{\pi}{4}, \frac{\pi}{4})$
  have harange (i : Fin (n + 1)) : a i - π / 4 ∈ Ioo (-π / 4) (π / 4) := by
    obtain h := ha i
    simp at h ⊢
    constructor
    · linarith only [h.1]
    · linarith only [h.2]

  -- Then we have that $$ \tan a_{i}=\tan \left(a_{i}-45^{\circ}+45^{\circ}\right)=\frac{x_{i}+1}{1-x_{i}} $$
  have hx (i : Fin (n + 1)) : tan (a i) = (x i + 1) / (1 - x i) := by
    rw [show a i = a i - π / 4 + π / 4 by simp]
    rw [tan_add, tan_pi_div_four, mul_one]
    apply Or.inl
    constructor <;> intro k
    · by_contra h
      obtain harange := harange i
      rw [h] at harange
      simp at harange
      have harange : -1 < (k : ℝ) ∧ (k : ℝ) < 0 := by
        constructor
        · calc
            -1 < - (3 : ℝ) / 4 := by norm_num
            _ = ((-π / 4) / (π / 2) - 1) / 2 := by field_simp; ring
            _ < ((2 * k + 1) * π / 2 / (π / 2) - 1) / 2 := by rel [harange.1]
            _ = k := by field_simp
        · calc
            (k : ℝ) = ((2 * k + 1) * π / 2 / (π / 2) - 1) / 2 := by field_simp
            _ < ((π / 4) / (π / 2) - 1) / 2 := by rel [harange.2]
            _ = - 1 / 4 := by field_simp; ring
            _ < 0 := by norm_num
      norm_cast at harange
      have : k ≥ 0 := by exact harange.1
      have : ¬ k ≥ 0 := by simp [harange.2]
      contradiction
    · by_contra h
      field_simp at h
      nth_rw 3 [mul_comm] at h
      rw [mul_assoc] at h
      simp [show ¬ π = 0 by exact pi_ne_zero] at h
      have hkeq : k = (-1) / (4 : ℝ) := by linarith [h]
      have : (k : ℝ) < 0 := by linarith
      norm_cast at this
      have : ¬ k < 0 := by
        suffices h : (k : ℝ) > -1
        · norm_cast at h
          simp
          exact h
        · rw [hkeq]
          norm_num
      contradiction

  -- Prove that $x_i \in (-1, 1)$
  have hxrange (i : Fin (n + 1)) : x i ∈ Set.Ioo (-1) 1 := by
    simp [x]
    obtain h := harange i
    simp at h
    have : π / 4 < π / 2 := by
      apply div_lt_div_iff_of_pos_left ?_ ?_ ?_ |>.mpr
      · norm_num
      · exact pi_pos
      · norm_num
      · norm_num
    constructor
    · rw [show -1 = tan (-π / 4) by rw [neg_div, tan_neg, tan_pi_div_four]]
      apply tan_lt_tan_of_lt_of_lt_pi_div_two
      · rw [neg_div]
        simp [this]
      · apply lt_trans h.2
        exact this
      · exact h.1
    · rw [show 1 = tan (π / 4) by rw [tan_pi_div_four]]
      apply tan_lt_tan_of_lt_of_lt_pi_div_two
      · apply lt_trans ?_ h.1
        rw [neg_div]
        simp [this]
      · exact this
      · exact h.2

  -- If we further substitute $y_{i}=\frac{1-x_{i}}{2}$,
  let y (i : Fin (n + 1)) := (1 - x i) / 2

  -- Prove that $y_i \in (0, 1)$
  have hyrange (i : Fin (n + 1)) : y i ∈ Set.Ioo 0 1 := by
    simp [y]
    obtain h := hxrange i
    simp at h
    constructor
    · exact h.2
    · linarith only [h.1]

  -- Prove that $\sum_{0}^{n} y_{i} \leq 1$ and $y_{i} \geq 0$,
  have hsumy : ∑ i, y i ≤ 1 := by
    simp [y]
    rw [←Finset.sum_div, Finset.sum_sub_distrib]
    simp
    linarith only [h]
  have hypos (i : Fin (n + 1)) : y i > 0 := by
    obtain h := hyrange i
    simp at h
    exact h.1
  have hyne (i : Fin (n + 1)) : y i ≠ 0 := by exact Ne.symm (ne_of_lt (hypos i))

  -- If n = 0, it is trivial
  by_cases hn : n = 0
  simp [hn]
  apply Finset.prod_nonneg
  intro i _
  obtain ha := ha i
  simp at ha
  apply tan_nonneg_of_nonneg_of_le_pi_div_two
  · exact le_of_lt ha.1
  · exact le_of_lt ha.2
  -- Then we have to prove that the following statement:
  -- Claim: If $\sum_{0}^{n} y_{i} \leq 1$ and $y_{i} \geq 0$,
  -- we have $$ \prod_{i=1}^{n}\left(\frac{1}{y_{i}}-1\right) \geq n^{n+1} $$ $$ \prod_{i=1}^{n}\left(\frac{y_{0}+y_{1}+y_{2}+\cdots+y_{n}}{y_{i}}-1\right) \geq n^{n+1} $$
  suffices h : ∏ i, ((∑ j, y j) / y i - 1) ≥ n ^ (n + 1)
  · -- Substitute tan (a i) with 1 / y_i - 1
    have hsub : ∀ i ∈ Finset.univ, tan (a i) = 1 / (y i) - 1 := by
      intro i _
      obtain h := hxrange i
      simp at h
      simp [y, hx i]
      rw [div_sub', mul_one, tsub_tsub_assoc]
      · norm_num
        rw [add_comm]
      · norm_num
      · apply le_of_lt
        exact h.2
      · apply ne_of_gt
        simp [h.2]
    -- Simplify the result
    rw [Finset.prod_congr rfl hsub]
    apply le_trans h
    apply Finset.prod_le_prod
    · intro i _
      simp
      apply le_div_iff₀ (hypos i) |>.mpr
      simp
      rw [show y i = ∑ j ∈ Finset.Icc i i, y j by simp]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro i _ _
        exact le_of_lt (hypos i)
    · intro i _
      field_simp
      apply div_le_div₀
      · norm_num
      · exact hsumy
      · exact hypos i
      · simp
  · -- Apply the AM-GM inequality
    have hge (i : Fin (n + 1)) (_ : i ∈ Finset.univ) : (∑ j : Fin (n + 1), y j) / y i - 1 ≥ (∏ j ∈ Finset.univ \ {i}, y j) ^ (1 / (n : ℝ)) / (y i) * n := by
      let s := Finset.univ \ {i}
      let w (i : Fin (n + 1)) := 1 / (n : ℝ)
      have hw : ∀ i ∈ s, 0 ≤ w i := by intro i _; simp [w]
      have hw' : 0 < ∑ i ∈ s, w i := by
        apply Finset.sum_pos
        · simp [w]
          intro i _
          exact Nat.zero_lt_of_ne_zero hn
        · simp [s]
          by_cases hi : i ≠ n
          · use n
            simp at hi ⊢
            exact fun a ↦ hi (id (Eq.symm a))
          · use 0
            simp at hi ⊢
            simp [hi, hn]
      have hz : ∀ i ∈ s, 0 ≤ y i := by
        intro i _
        exact le_of_lt (hypos i)
      obtain h := geom_mean_le_arith_mean s w y hw hw' hz
      simp [w] at h
      have : s.card = n := by
        rw [Finset.card_sdiff]
        · simp
        · simp
      rw [this, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), rpow_one, div_one] at h
      calc
        (∑ j : Fin (n + 1), y j) / y i - 1 = (∑ j ∈ s, y j) / y i := by
          apply eq_div_iff (hyne i) |>.mpr
          rw [sub_mul, div_mul_cancel₀ _ (hyne i), one_mul]
          simp [s]
        _ = (∑ x ∈ s, (n : ℝ)⁻¹ * y x) * n / y i:= by
          field_simp
          rw [Finset.sum_mul]
          congr
          ext i
          rw [div_mul_cancel₀]
          norm_cast
        _ ≥ (∏ x ∈ s, y x ^ (n : ℝ)⁻¹) * n / y i := by
          apply div_le_div_of_nonneg_right
          · rel [h]
          · exact le_of_lt (hypos i)
        _ ≥ (∏ j ∈ Finset.univ \ {i}, y j) ^ (1 / (n : ℝ)) / y i * ↑n := by
          field_simp
          apply div_le_div_of_nonneg_right
          · rw [←finset_prod_rpow]
            intro j _
            exact le_of_lt (hypos j)
          · exact le_of_lt (hypos i)
    -- Prove the product of RHS is exactly (∏ x : Fin (n + 1), y x) ^ (n : ℝ)
    have hprod : ∏ i : Fin (n + 1), (∏ j ∈ Finset.univ \ {i}, y j) = (∏ x : Fin (n + 1), y x) ^ (n : ℝ) := by
      have (i : Fin (n + 1)) (_ : i ∈ Finset.univ) : ∏ j ∈ Finset.univ \ {i}, y j = (∏ j, y j) / y i := by
        rw [←Finset.prod_sdiff (show {i} ⊆ Finset.univ by simp)]
        simp
        rw [mul_div_cancel_right₀]
        exact hyne i
      rw [Finset.prod_congr rfl this, Finset.prod_div_distrib]
      simp
      rw [pow_add, pow_one, mul_div_cancel_right₀]
      apply ne_of_gt
      apply Finset.prod_pos
      intro i _
      exact hypos i
    calc
      ∏ i : Fin (n + 1), ((∑ j : Fin (n + 1), y j) / y i - 1) ≥ ∏ i : Fin (n + 1), ((∏ j ∈ Finset.univ \ {i}, y j) ^ (1 / (n : ℝ)) / (y i) * n) := by
        -- Apply the inequality
        apply Finset.prod_le_prod
        · intro i _
          apply mul_nonneg
          · apply mul_nonneg
            · apply rpow_nonneg
              apply Finset.prod_nonneg
              exact fun i _ => le_of_lt (hypos i)
            · simp
              exact le_of_lt (hypos i)
          · simp
        · exact hge
      -- Simplify the result
      _ = n ^ (n + 1) * ∏ i : Fin (n + 1), ((∏ j ∈ Finset.univ \ {i}, y j) ^ (1 / (n : ℝ)) / (y i)) := by
        rw [Finset.prod_mul_distrib]
        simp
        ring
      _ = n ^ (n + 1) * 1 := by
        simp only [mul_eq_mul_left_iff]
        apply Or.inl
        rw [Finset.prod_div_distrib, finset_prod_rpow, hprod, ←rpow_mul, mul_div_cancel₀, rpow_one, div_self]
        · apply ne_of_gt
          apply Finset.prod_pos
          exact fun i _ => hypos i
        · simp [hn]
        · apply Finset.prod_nonneg
          exact fun i _ => le_of_lt (hypos i)
        · intro i _
          apply Finset.prod_nonneg
          exact fun i _ => le_of_lt (hypos i)
      _ = n ^ (n + 1) := by simp
